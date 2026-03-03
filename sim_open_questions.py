"""Simulations for open questions and worked examples.

Experiment A: Compute δ₀ and the perturbative threshold for a specific (E, S).
             Gives a concrete worked example for the proposition.

Experiment B: Empirical T* (time to capture inertness) vs ||K|| and |X|.
             Characterizes Q3 (rate of approach to inertness).

Experiment C: Near-degenerate E (small angular separation).
             Probes Q4 (what happens when genericity fails).

Experiment D: δ₀ vs S direction — how does the gap vary?
"""

import sys
sys.path.insert(0, ".")

import torch
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from sra.config.schema import SRAConfig
from sra.core.system import SRASystem


def compute_delta_0(E, S, n_steps=3000):
    """Run K=0 system, find q*₀, compute δ₀ and σ_min."""
    n, d = E.shape
    config = SRAConfig(
        n_stimuli=n, embed_dim=d,
        E=E.clone(), K=torch.zeros(d, d),
        S=S.clone(), record_history=False,
        capture_enabled=True, consolidation_enabled=True,
    )
    sys = SRASystem(config)

    for t in range(n_steps):
        state = sys.step()

    q_star = state.q.detach()
    sigma_star = state.sigma.detach()
    sigma_min = sigma_star.min().item()

    # Score gap at q*₀
    scores = q_star @ E.T  # (n,)
    sorted_scores, _ = scores.sort(descending=True)
    delta_0 = (sorted_scores[0] - sorted_scores[1]).item()
    tau_star = scores.argmax().item()

    R = E.norm(dim=1).max().item()

    # Perturbative threshold
    threshold = delta_0 / (4 * R**4 * (1 + 1/sigma_min))

    return {
        'q_star': q_star,
        'sigma_star': sigma_star,
        'sigma_min': sigma_min,
        'delta_0': delta_0,
        'tau_star': tau_star,
        'R': R,
        'threshold': threshold,
        'scores': scores.detach(),
    }


def find_T_star(E, S, K_scale, n_steps=2000):
    """Run system, return T* (last capture time) or None if still active."""
    n, d = E.shape
    K = K_scale * torch.eye(d)
    config = SRAConfig(
        n_stimuli=n, embed_dim=d,
        E=E.clone(), K=K, S=S.clone(),
        record_history=False,
        capture_enabled=True, consolidation_enabled=True,
    )
    sys = SRASystem(config)

    last_capture = None
    prev_M = 0
    for t in range(n_steps):
        state = sys.step()
        m = state.M.shape[0]
        if m > prev_M and t > 0:
            last_capture = t
        prev_M = m

    if last_capture is None:
        return 0  # no captures at all (cold start only)
    if last_capture > n_steps - 100:
        return None  # still active
    return last_capture


# ========================================================================
# Experiment A: Worked example
# ========================================================================
def experiment_A():
    print("=" * 70)
    print("EXPERIMENT A: Worked numerical example")
    print("=" * 70)

    torch.manual_seed(42)
    n, d = 10, 8
    E = torch.randn(n, d)
    E = E / E.norm(dim=1, keepdim=True)  # R = 1

    S = torch.zeros(n)
    S[0] = 1.0

    info = compute_delta_0(E, S)

    print(f"\n  Parameters: |X| = {n}, d = {d}, R = {info['R']:.4f}")
    print(f"  S: stimulus 0 preferred (S[0] = 1)")
    print(f"\n  K = 0 equilibrium:")
    print(f"    q*₀ direction: τ* = {info['tau_star']}")
    print(f"    σ_min = {info['sigma_min']:.6f}")
    print(f"    δ₀ = {info['delta_0']:.6f}")
    print(f"\n  Perturbative threshold:")
    print(f"    ||K|| < δ₀ / (4R⁴(1 + 1/σ_min))")
    print(f"           = {info['delta_0']:.6f} / (4 × {info['R']:.4f}⁴ × (1 + 1/{info['sigma_min']:.4f}))")
    print(f"           = {info['threshold']:.6f}")

    # Verify: test K values around the threshold
    print(f"\n  Verification (T* = last capture time, 2000 steps):")
    test_K = [0.0, info['threshold']*0.5, info['threshold'],
              info['threshold']*2, info['threshold']*5, info['threshold']*10]
    for k in test_K:
        T_star = find_T_star(E, S, k)
        status = f"T* = {T_star}" if T_star is not None else "STILL ACTIVE"
        marker = " ← threshold" if abs(k - info['threshold']) < 1e-8 else ""
        print(f"    ||K|| = {k:.6f}: {status}{marker}")

    # Score gap distribution at q*₀
    print(f"\n  Score distribution at q*₀:")
    scores = info['scores']
    sorted_s, sorted_idx = scores.sort(descending=True)
    for i in range(min(5, n)):
        print(f"    τ={sorted_idx[i].item()}: score = {sorted_s[i].item():.6f}"
              f"{'  ← argmax' if i == 0 else f'  (gap = {sorted_s[0].item() - sorted_s[i].item():.6f})'}")

    return info


# ========================================================================
# Experiment B: T* vs ||K|| and |X|
# ========================================================================
def experiment_B():
    print(f"\n{'=' * 70}")
    print("EXPERIMENT B: T* (inertness time) vs ||K|| and |X|")
    print("=" * 70)

    results = {}

    for n_stimuli in [5, 10, 20, 50]:
        torch.manual_seed(42)
        d = 8
        E = torch.randn(n_stimuli, d)
        E = E / E.norm(dim=1, keepdim=True)
        S = torch.zeros(n_stimuli)
        S[0] = 1.0

        info = compute_delta_0(E, S)
        thresh = info['threshold']

        K_vals = np.logspace(-3, 1, 30)
        T_stars = []
        for k in K_vals:
            T_star = find_T_star(E, S, float(k), n_steps=1000)
            T_stars.append(T_star)

        results[n_stimuli] = (K_vals, T_stars, thresh)

        print(f"\n  |X| = {n_stimuli}, δ₀ = {info['delta_0']:.4f}, "
              f"σ_min = {info['sigma_min']:.4f}, threshold = {thresh:.4f}")
        # Find empirical critical K
        empirical_crit = None
        for i, (k, t) in enumerate(zip(K_vals, T_stars)):
            if t is None:
                empirical_crit = K_vals[i-1] if i > 0 else None
                break
        if empirical_crit is not None:
            print(f"  Empirical critical ||K||: ≈ {empirical_crit:.4f} "
                  f"(threshold = {thresh:.4f}, ratio = {empirical_crit/thresh:.1f}×)")
        else:
            print(f"  Capture inert for all tested ||K|| (max = {K_vals[-1]:.2f})")

    return results


# ========================================================================
# Experiment C: Near-degenerate E
# ========================================================================
def experiment_C():
    print(f"\n{'=' * 70}")
    print("EXPERIMENT C: Near-degenerate E (small angular separation)")
    print("=" * 70)

    d = 8

    for n_stimuli in [5, 10]:
        print(f"\n  |X| = {n_stimuli}:")

        for spread in [1.0, 0.5, 0.1, 0.01]:
            torch.manual_seed(42)
            # Base direction
            base = torch.randn(d)
            base = base / base.norm()
            # Perturb slightly
            E = base.unsqueeze(0).repeat(n_stimuli, 1)
            noise = torch.randn(n_stimuli, d) * spread
            E = E + noise
            E = E / E.norm(dim=1, keepdim=True)

            S = torch.zeros(n_stimuli)
            S[0] = 1.0

            info = compute_delta_0(E, S, n_steps=5000)

            # Test a few K values
            T_at_01 = find_T_star(E, S, 0.1)
            T_at_1 = find_T_star(E, S, 1.0)

            print(f"    spread={spread:.2f}: δ₀={info['delta_0']:.6f}, "
                  f"σ_min={info['sigma_min']:.4f}, "
                  f"threshold={info['threshold']:.6f}, "
                  f"T*(K=0.1)={T_at_01}, T*(K=1)={T_at_1}")


# ========================================================================
# Experiment D: δ₀ vs S direction
# ========================================================================
def experiment_D():
    print(f"\n{'=' * 70}")
    print("EXPERIMENT D: δ₀ vs preferred stimulus (varying S)")
    print("=" * 70)

    torch.manual_seed(42)
    n, d = 10, 8
    E = torch.randn(n, d)
    E = E / E.norm(dim=1, keepdim=True)

    print(f"\n  {'S[τ]=1':>10s}  {'τ*':>4s}  {'δ₀':>10s}  {'σ_min':>8s}  {'threshold':>10s}")
    print(f"  {'─' * 48}")

    deltas = []
    thresholds = []
    for tau in range(n):
        S = torch.zeros(n)
        S[tau] = 1.0
        info = compute_delta_0(E, S)
        deltas.append(info['delta_0'])
        thresholds.append(info['threshold'])
        print(f"  τ={tau:8d}  {info['tau_star']:4d}  {info['delta_0']:10.6f}  "
              f"{info['sigma_min']:8.4f}  {info['threshold']:10.6f}")

    print(f"\n  Summary:")
    print(f"    min δ₀ = {min(deltas):.6f} (worst case)")
    print(f"    max δ₀ = {max(deltas):.6f} (best case)")
    print(f"    min threshold = {min(thresholds):.6f}")
    print(f"    max threshold = {max(thresholds):.6f}")


def main():
    info = experiment_A()
    results_B = experiment_B()
    experiment_C()
    experiment_D()


if __name__ == "__main__":
    main()
