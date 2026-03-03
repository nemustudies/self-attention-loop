"""
Reference implementation of the five-step loop from
"A Math Loop That Sleeps and Dreams" (nemu, 2026).

Implements Definitions 1-6: OBSERVE, ACCUMULATE, RETRIEVE, CONSOLIDATE, CAPTURE.
All operations are GPU-native via PyTorch.
"""

import torch
from torch.nn.functional import softmax


def step(C, N, M, E, K, t, ell=None,
         phi=lambda x: softmax(x, dim=-1),
         lam=lambda r: 1 - r):
    """
    One iteration: Definitions 1-6.

    C:     (|X|,)         cumulative contrast, C_0 > 0
    N:     (|X|,)         lifetime count
    M:     (m, d)         impression matrix, m = 0 initially
    E:     (|X|, d)       embeddings
    K:     (d, d)         linear projection
    t:     int            step index
    ell:   (d,) or None   retrieval vector from previous step
    """

    # Definition 1: scoring from previous retrieval
    sigma = C / N.clamp(min=1)
    if ell is not None:
        b = E @ (K @ ell)                                    # (|X|,)
    else:
        b = torch.zeros_like(sigma)
    S = sigma + b                                            # scoring is purely feedback

    # Definition 2: observation
    a = phi(S)                                               # (|X|,)

    # Definition 3: accumulation
    C = C + a * (t + 1) / C
    N = N + 1
    sigma = C / N

    # Definition 4: retrieval
    q = a @ E                                                # (d,)
    if M.shape[0] > 0:
        scores = q @ M.T                                     # (m,)
        w = phi(scores.unsqueeze(0)).squeeze(0)               # (m,)
        ell = w @ M                                          # (d,)

        # Definition 5: consolidation
        blend = lam(w / w.max()).unsqueeze(-1)                # (m, 1)
        target = phi(((M + q) @ M.T)) @ M                   # (m, d)
        M = (1 - blend) * M + blend * target

        # Definition 6: capture
        novelty = q @ E.T                                    # (|X|,)
        mask = novelty > scores.max()
        if mask.any():
            M = torch.cat([M, E[mask]])
    else:
        # Cold start: max over empty set is -inf, everything admitted
        M = E.clone()
        ell = None

    return C, N, M, ell
