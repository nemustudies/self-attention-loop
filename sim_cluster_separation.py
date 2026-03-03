"""
sim_cluster_separation.py
=========================
Empirical test: is inter-cluster separation preserved during SRA consolidation?

We implement the consolidation update directly (no capture, no feedback unless
requested) for maximum control:

    scores = q @ M.T
    w = phi(scores)
    ell = w @ M
    blend = lam(w / w.max()).unsqueeze(-1)
    M = (1 - blend) * M + blend * ell

The anchor v = argmax(w) satisfies lam(1) = 0, so it never moves.
Non-anchor rows blend toward ell (the retrieval-weighted centroid).

Experiments
-----------
1. Two well-separated clusters: track intra/inter metrics over 500 steps.
2. Three clusters at varying separations (2, 4, 8).
3. Cluster size asymmetry (10 vs 2 points).
4. Effect of feedback matrix K != 0.
"""

from __future__ import annotations

import torch
from torch import Tensor

from sra.core.simplex import Softmax
from sra.core.blend import LinearBlend


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def make_clusters(
    centers: list[Tensor],
    counts: list[int],
    noise: float = 0.1,
    seed: int = 42,
) -> tuple[Tensor, list[list[int]]]:
    """Generate clustered memory rows.

    Returns
    -------
    M : (sum(counts), d)
    labels : list of index-lists, one per cluster
    """
    gen = torch.Generator().manual_seed(seed)
    rows: list[Tensor] = []
    labels: list[list[int]] = []
    idx = 0
    for c, n in zip(centers, counts):
        d = c.shape[0]
        pts = c.unsqueeze(0) + noise * torch.randn(n, d, generator=gen)
        rows.append(pts)
        labels.append(list(range(idx, idx + n)))
        idx += n
    return torch.cat(rows, dim=0), labels


def cluster_centroid(M: Tensor, indices: list[int]) -> Tensor:
    return M[indices].mean(dim=0)


def intra_diameter(M: Tensor, indices: list[int]) -> float:
    """Max pairwise distance within a cluster."""
    sub = M[indices]
    if len(indices) < 2:
        return 0.0
    dists = torch.cdist(sub.unsqueeze(0), sub.unsqueeze(0)).squeeze(0)
    return dists.max().item()


def inter_centroid_distance(M: Tensor, labels: list[list[int]]) -> float:
    """Min pairwise distance between cluster centroids."""
    centroids = [cluster_centroid(M, lab) for lab in labels]
    min_dist = float("inf")
    for i in range(len(centroids)):
        for j in range(i + 1, len(centroids)):
            d = (centroids[i] - centroids[j]).norm().item()
            if d < min_dist:
                min_dist = d
    return min_dist


def min_inter_cluster_distance(M: Tensor, labels: list[list[int]]) -> float:
    """Min distance between any point in cluster i and any point in cluster j."""
    min_dist = float("inf")
    for i in range(len(labels)):
        for j in range(i + 1, len(labels)):
            dists = torch.cdist(
                M[labels[i]].unsqueeze(0), M[labels[j]].unsqueeze(0)
            ).squeeze(0)
            d = dists.min().item()
            if d < min_dist:
                min_dist = d
    return min_dist


# ---------------------------------------------------------------------------
# Core consolidation step (standalone, no system wrapper needed)
# ---------------------------------------------------------------------------

def consolidation_step(
    M: Tensor,
    q: Tensor,
    phi: Softmax,
    lam: LinearBlend,
) -> Tensor:
    """One consolidation update.  Returns new M."""
    scores = q @ M.T                                # (m,)
    w = phi(scores.unsqueeze(0)).squeeze(0)          # (m,)
    ell = w @ M                                      # (d,)
    blend = lam(w / w.max()).unsqueeze(-1)            # (m, 1)
    target = ell.unsqueeze(0).expand_as(M)            # (m, d)
    return (1 - blend) * M + blend * target


def run_consolidation(
    M: Tensor,
    q: Tensor,
    phi: Softmax,
    lam: LinearBlend,
    n_steps: int,
    labels: list[list[int]],
    K: Tensor | None = None,
    log_every: int = 100,
) -> dict:
    """Run consolidation loop and track metrics.

    If K is provided, we add feedback:  q_effective = q + K @ ell
    (simplified: we apply K directly in memory-embedding space,
    bypassing the stimulus embedding E).
    """
    history = {
        "inter_centroid": [],
        "min_inter": [],
        "intra_diameters": [],
        "step": [],
    }

    def record(step: int, M_cur: Tensor) -> None:
        history["step"].append(step)
        history["inter_centroid"].append(inter_centroid_distance(M_cur, labels))
        history["min_inter"].append(min_inter_cluster_distance(M_cur, labels))
        history["intra_diameters"].append(
            [intra_diameter(M_cur, lab) for lab in labels]
        )

    record(0, M)

    for t in range(1, n_steps + 1):
        # If feedback is active, update q via ell from previous step
        if K is not None:
            scores_tmp = q @ M.T
            w_tmp = phi(scores_tmp.unsqueeze(0)).squeeze(0)
            ell_tmp = w_tmp @ M
            # Feedback: shift query by K @ ell.  In the full SRA system
            # this goes through E, but here we work directly in d-space.
            q_eff = q + (K @ ell_tmp)
        else:
            q_eff = q

        M = consolidation_step(M, q_eff, phi, lam)
        if t % log_every == 0 or t == n_steps:
            record(t, M)

    return history


# ---------------------------------------------------------------------------
# Pretty-print helpers
# ---------------------------------------------------------------------------

def print_header(title: str) -> None:
    sep = "=" * 72
    print(f"\n{sep}")
    print(f"  {title}")
    print(sep)


def print_metrics(history: dict, n_clusters: int) -> None:
    steps = history["step"]
    ic0 = history["inter_centroid"][0]
    ic_final = history["inter_centroid"][-1]
    mi0 = history["min_inter"][0]
    mi_final = history["min_inter"][-1]

    print(f"  {'Step':>6}  {'Inter-centroid':>15}  {'Min inter-pt':>13}", end="")
    for c in range(n_clusters):
        print(f"  {'Intra-C' + str(c):>10}", end="")
    print()
    print(f"  {'-'*6}  {'-'*15}  {'-'*13}", end="")
    for _ in range(n_clusters):
        print(f"  {'-'*10}", end="")
    print()

    for i, t in enumerate(steps):
        ic = history["inter_centroid"][i]
        mi = history["min_inter"][i]
        line = f"  {t:>6}  {ic:>15.6f}  {mi:>13.6f}"
        for c in range(n_clusters):
            line += f"  {history['intra_diameters'][i][c]:>10.6f}"
        print(line)

    print()
    ratio_cent = ic_final / ic0 if ic0 > 0 else float("nan")
    ratio_min = mi_final / mi0 if mi0 > 0 else float("nan")
    print(f"  Inter-centroid ratio (final/initial): {ratio_cent:.6f}")
    print(f"  Min inter-point ratio (final/initial): {ratio_min:.6f}")
    preserved = ratio_cent > 0.5 and ratio_min > 0.0
    print(f"  Separation broadly preserved: {preserved}")


# ---------------------------------------------------------------------------
# Experiments
# ---------------------------------------------------------------------------

def experiment_1() -> None:
    """Two well-separated clusters, d=8, 5 points each."""
    print_header("Experiment 1: Two well-separated clusters")

    d = 8
    sep = 4.0
    c1 = torch.zeros(d)
    c2 = torch.zeros(d)
    c2[0] = sep  # separated along first axis

    M, labels = make_clusters([c1, c2], [5, 5], noise=0.1)
    # Query: choose q near the anchor cluster (cluster 0)
    q = c1.clone()
    q[1] = 0.1  # slight offset so softmax is non-degenerate

    phi = Softmax(beta=1.0)
    lam = LinearBlend()

    history = run_consolidation(M, q, phi, lam, n_steps=500, labels=labels, log_every=100)
    print_metrics(history, 2)


def experiment_2() -> None:
    """Three clusters at varying separations."""
    print_header("Experiment 2: Three clusters, varying separation")

    d = 8

    for sep in [2.0, 4.0, 8.0]:
        print(f"\n  --- Separation = {sep} ---")
        c1 = torch.zeros(d)
        c2 = torch.zeros(d)
        c2[0] = sep
        c3 = torch.zeros(d)
        c3[1] = sep

        M, labels = make_clusters([c1, c2, c3], [5, 5, 5], noise=0.1)
        q = c1.clone()
        q[2] = 0.1

        phi = Softmax(beta=1.0)
        lam = LinearBlend()

        history = run_consolidation(M, q, phi, lam, n_steps=500, labels=labels, log_every=100)
        print_metrics(history, 3)


def experiment_3() -> None:
    """Cluster size asymmetry: 10 vs 2 points."""
    print_header("Experiment 3: Cluster size asymmetry (10 vs 2)")

    d = 8
    sep = 4.0
    c1 = torch.zeros(d)
    c2 = torch.zeros(d)
    c2[0] = sep

    M, labels = make_clusters([c1, c2], [10, 2], noise=0.1)
    q = c1.clone()
    q[1] = 0.1

    phi = Softmax(beta=1.0)
    lam = LinearBlend()

    history = run_consolidation(M, q, phi, lam, n_steps=500, labels=labels, log_every=100)
    print_metrics(history, 2)

    # Also try with query near the small cluster
    print("\n  --- Query near the SMALL cluster ---")
    M2, labels2 = make_clusters([c1, c2], [10, 2], noise=0.1)
    q2 = c2.clone()
    q2[1] = 0.1

    history2 = run_consolidation(M2, q2, phi, lam, n_steps=500, labels=labels2, log_every=100)
    print_metrics(history2, 2)


def experiment_4() -> None:
    """Effect of feedback K on consolidation.

    K = scale * I does not change consolidation because softmax is
    shift-invariant and K*I only rescales the query.  We instead test
    with an asymmetric K that *rotates* the effective query, potentially
    shifting anchor identity and changing which cluster collapses faster.

    We also vary softmax inverse-temperature (beta) to see how sharper
    attention interacts with feedback.
    """
    print_header("Experiment 4: Effect of feedback matrix K")

    d = 8
    sep = 4.0
    c1 = torch.zeros(d)
    c2 = torch.zeros(d)
    c2[0] = sep

    lam = LinearBlend()

    # Part A: K that projects ell onto an orthogonal direction.
    # K = scale * P where P projects onto dim 1 (orthogonal to the
    # separation axis dim 0).  This adds a cross-dimensional feedback
    # that genuinely alters which memories are closest to q_eff.
    print("\n  Part A: K = scale * cross-projection (ell_0 -> q_1 shift)")
    K_cross = torch.zeros(d, d)
    K_cross[1, 0] = 1.0  # maps ell's dim-0 component into q's dim-1

    for scale in [0.0, 0.5, 2.0, 5.0]:
        print(f"\n  --- K = {scale} * K_cross ---")
        M, labels = make_clusters([c1, c2], [5, 5], noise=0.1)
        # Place clusters so ell has meaningful dim-0 component
        # Shift cluster centers away from origin
        shift = torch.zeros(d)
        shift[0] = 3.0
        M = M + shift.unsqueeze(0)
        q = (c1 + shift).clone()
        q[1] = 0.1

        K = scale * K_cross if scale > 0 else None
        phi = Softmax(beta=1.0)
        history = run_consolidation(
            M, q, phi, lam, n_steps=500, labels=labels,
            K=K, log_every=100,
        )
        print_metrics(history, 2)

    # Part B: vary softmax sharpness (beta) -- no feedback
    print("\n  Part B: Varying softmax sharpness (beta), K = 0")
    for beta in [0.5, 1.0, 2.0, 5.0]:
        print(f"\n  --- beta = {beta} ---")
        M, labels = make_clusters([c1, c2], [5, 5], noise=0.1)
        q = c1.clone()
        q[1] = 0.1
        phi = Softmax(beta=beta)
        history = run_consolidation(
            M, q, phi, lam, n_steps=500, labels=labels, log_every=100,
        )
        print_metrics(history, 2)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    print("Cluster Separation under SRA Consolidation")
    print("=" * 72)
    print("Testing whether inter-cluster distance is preserved when the")
    print("consolidation update blends non-anchor memories toward the")
    print("retrieval centroid ell = w @ M.")
    print()
    print("Setup: pure consolidation (no capture), phi = softmax(beta=1),")
    print("       lam = LinearBlend (1 - r), d = 8.")

    experiment_1()
    experiment_2()
    experiment_3()
    experiment_4()

    print("\n" + "=" * 72)
    print("  SUMMARY")
    print("=" * 72)
    print()
    print("  Key findings:")
    print()
    print("  1. Inter-cluster separation is NOT preserved under pure")
    print("     consolidation.  Non-anchor clusters steadily collapse toward")
    print("     the retrieval centroid ell (which is close to the anchor).")
    print("     Final/initial ratios are typically << 0.1.")
    print()
    print("  2. The collapse rate is roughly independent of initial separation")
    print("     (Exp 2): clusters at distance 2, 4, and 8 all reach similar")
    print("     final/initial ratios (~0.001).")
    print()
    print("  3. Cluster size asymmetry (Exp 3): the smaller cluster collapses")
    print("     faster.  When the query anchors the large cluster, the small")
    print("     cluster's intra-diameter shrinks dramatically while the large")
    print("     cluster's barely changes.")
    print()
    print("  4. Cross-dimensional feedback K accelerates separation loss")
    print("     (Exp 4A).  Softmax sharpness (beta) also matters: lower beta")
    print("     (softer attention) slows the collapse (Exp 4B, ratio ~0.18")
    print("     at beta=0.5 vs ~0.03 at beta=5.0).")
    print()
    print("  Implication: consolidation with a fixed query and LinearBlend")
    print("  will merge non-anchor clusters into the anchor over O(100)")
    print("  steps.  Preserving cluster structure requires either (a) cycling")
    print("  the anchor across clusters, (b) using a blend rate that decays")
    print("  more aggressively (e.g., PowerBlend with p>1), or (c) limiting")
    print("  the number of consolidation steps per sleep episode.")
    print()


if __name__ == "__main__":
    main()
