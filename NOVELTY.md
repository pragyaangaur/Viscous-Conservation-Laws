# Novelty check

Done on 6 October 2026 by reading the closest papers and searching for each main claim. The search was careful but not exhaustive, so treat the "new" column as "not found", and repeat the check before submitting.

## Claim by claim

| Claim | Status | Closest prior work |
| --- | --- | --- |
| Differential identity for Q and P under heavy ball, `d/dt(γQ + 2mP) = 2mK` | Known in substance | Tanaka and Kunin, NeurIPS 2021, give the general Noether learning dynamics with damping for any symmetry and Bregman Lagrangian. Kunin et al., ICLR 2021, give the equations for scale and rescale symmetries under momentum and solve them with a Green's function. |
| Exact time-dependent laws for skew-symmetric generators | Known | Marcotte, Gribonval and Peyré, ICML 2024. In our framework these are the case K = 0. |
| Momentum destroys all laws of ReLU networks | Known | Marcotte, Gribonval and Peyré, ICML 2024. |
| Drift bound for plain gradient descent | Known | Du, Hu and Lee, NeurIPS 2018. Medeiros, arXiv 2604.07405, 2026, studies the step-size scaling near the edge of stability. |
| η/(1−β)² as the controlling quantity | Known for diagonal linear networks | Papazov, Pesme and Flammarion, AISTATS 2024. Our bound extends it to every network with a linear symmetry. |
| Uniform-in-time drift bound 2m‖A‖(L₀ − L∞)/γ² for heavy ball | Not found | Marcotte et al. 2024 say they give no drift bounds and leave discrete time open. Kunin et al. give exact Green's-function forms but no energy bound. |
| Sharpness via scale-invariant parameters | Not found | Arora, Li and Lyu, ICLR 2019, and Wan et al., NeurIPS 2021, study norm growth of scale-invariant weights under momentum but not this equality. |
| First-order formula in the mass, with proof | Not found | Josz and Li, arXiv 2407.15044, 2024, prove that heavy ball preserves boundedness as the mass vanishes. We use that to verify our hypothesis (H1). |
| Exact discrete identity with weights (1+β−2β^(N−j))/(1−β) | Not found | Kunin et al. treat discrete momentum through modified equations, not exact identities. |
| Exact identity for Nesterov's method with gradient at the extrapolated point | Not found | |
| Nesterov's schedule keeps a step-independent drift for PSD generators, heavy ball's vanishes | Not found | Lyu et al., AAAI 2025, study Nesterov with fixed momentum only. Papazov et al. study heavy ball. |
| Nuclear-norm bound for linear networks under heavy ball | Not found | |
| Lean formalisation | Not found for this topic | A separate `heavy-ball-lean` library formalises heavy ball convergence for strongly convex functions, which is a different result. |

## Papers read

- Kunin et al., Neural Mechanics, ICLR 2021, arXiv 2012.04728. Appendix on momentum read in full.
- Tanaka and Kunin, Noether's Learning Dynamics, NeurIPS 2021, arXiv 2105.02716.
- Marcotte, Gribonval and Peyré, Keep the Momentum, ICML 2024, arXiv 2405.12888.
- Papazov, Pesme and Flammarion, AISTATS 2024, arXiv 2403.05293.
- Lyu, Wang, Wang and Zhu, AAAI 2025.
- Wan, Zhu, Zhang and Sun, Spherical Motion Dynamics, arXiv 2006.08419.
- Josz and Li, Singular perturbation in heavy ball dynamics, arXiv 2407.15044.
- Abstracts only: Medeiros, arXiv 2604.07405; Nguyen and Montúfar, arXiv 2609.34549; Lyu et al., arXiv 2506.14806; Zhang and Lin, arXiv 2605.18528.

## What this means for the paper

The differential identity in Theorem 1 is credited to Tanaka and Kunin and to Kunin et al. The paper's new content is the quantitative layer on top of it: the bounds, their sharpness, the exact discrete weights, the Nesterov identity and dichotomy, the first-order formula, and the formalisation.
