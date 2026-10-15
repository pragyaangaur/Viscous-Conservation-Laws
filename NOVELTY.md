# Novelty check

First done on 6 October 2026 and repeated three times on 13 October 2026. In the last pass the full text of 29 papers was downloaded from arXiv and searched, including every paper that earlier passes had judged from an abstract or a summary. Every passage mentioning momentum, Nesterov, heavy ball, drift, discretisation or Lean was read in context. Across the passes, seven results turned out to be known in whole or in part, and each is credited in the paper. The search is still not exhaustive, so "not found" means exactly that.

## Claim by claim

| Claim | Status | Closest prior work |
| --- | --- | --- |
| Differential identity for Q and P under heavy ball, `d/dt(γQ + 2mP) = 2mK` | Known in substance | Tanaka and Kunin, NeurIPS 2021, give the Noether learning dynamics with damping for any symmetry and Bregman Lagrangian. Kunin et al., ICLR 2021, give the equations for scale and rescale symmetries under momentum and solve them with a Green's function. Neither gives a bound. |
| Exact time-dependent laws for skew-symmetric generators | Known | Marcotte, Gribonval and Peyré, ICML 2024. In our framework these are the case K = 0. |
| Momentum destroys all laws of ReLU networks | Known | Marcotte, Gribonval and Peyré, ICML 2024. |
| Gradient descent identity ΔQ = η²⟨∇L, A∇L⟩ for a general symmetric A, and monotone growth when A ⪰ 0 | Known | Ziyin, Wang, Li and Wu, NeurIPS 2024, Appendix D, eqs. (96) to (98). Zhao et al., ICLR 2023, Proposition E.1, bound it for two-layer linear networks. This is our β = 0 case. |
| Drift bound for plain (stochastic) gradient descent | Known | Du, Hu and Lee, NeurIPS 2018. Marcotte, Gribonval and Peyré, arXiv 2506.06194, Proposition 5.1, for SGD. Medeiros, arXiv 2604.07405, near the edge of stability. None of them treats momentum. |
| η/(1−β)² as the controlling quantity | Known for diagonal linear networks | Papazov, Pesme and Flammarion, AISTATS 2024. Our bound extends it to every network with a linear symmetry. |
| Uniform-in-time drift bound 2m‖A‖(L₀ − L∞)/γ² for heavy ball | Not found, and asked for | Marcotte et al., ICML 2024, Appendix N, observe in experiments on a ReLU MLP and on NMF that the quantities "stay bounded for all time within a range depending on the momentum parameter" and call a theoretical analysis future work. Our Theorem 1 gives it for every Euclidean quadratic law. Kunin et al. and Tanaka and Kunin give no bound. |
| Sharpness via scale-invariant parameters | Not found as a statement about the bound | Arora, Li and Lyu, ICLR 2019; Li and Arora, ICLR 2020; Heo et al. (AdamP), ICLR 2021; Wan et al., NeurIPS 2021. All study norm growth of scale-invariant weights under momentum. None states that this case attains a drift bound for general generators. |
| Exact discrete identity with weights (1+β−2β^(N−j))/(1−β) | Known for A = I, not found for general A | Heo et al. (AdamP), ICLR 2021, Lemma 2.2 and Corollary 2.3, give the identity for the squared norm of scale-invariant weights, with asymptotic factor 1 + 2β/(1−β) = (1+β)/(1−β). The general case, where K_j has both signs, and the bounds built on it were not found. |
| First-order formula in the mass | Formula known formally. Rigorous infinite-time limit not found | The slow-manifold expansion γθ' = −∇L − (m/γ²)∇²L∇L + O(m²), constructed to any order by Farazmand (SIAM J. Optim. 2020), gives the formula in one line. In discrete time, inserting the modified flow of Ghosh et al., ICLR 2023, eq. (4), gives exactly our first-order prediction (1+β)ηI/(1−β)². Kovachki and Stuart, JMLR 2021, have the same invariant manifold. All of these hold on finite horizons or near a minimum. Josz and Li, arXiv 2407.15044, prove a zeroth-order infinite-horizon result (Corollary 1: uniform convergence on [t₀, ∞) to gradient flow from a shifted start) and give an example that fails without a hypothesis like our (H2). The new part of Theorem 3 is the first-order term at t = ∞. |
| Integrated identity for Q under the Nesterov ODE, `d/dt(Q + 2tP/(r−1)) = 2tK/(r−1)` | Known in substance | Gluch and Urbanke, arXiv 2104.05508, Tables 2 and 4, give the balance equations with Ẅ + (3/t)Ẇ. Marcotte et al., ICML 2024, find the polynomial-in-t laws for skew generators. The energy identity and the bound with the weight t were not found. |
| Exact identity for Nesterov's method with the gradient at the extrapolated point | Not found | AdamP covers heavy ball only and says in one sentence that its observation also applies to Nesterov, with no formula. Lyu et al., AAAI 2025, and Kovachki and Stuart treat Nesterov with fixed momentum through modified flows. |
| Nesterov's schedule keeps a step-independent drift for PSD generators, heavy ball's vanishes | Not found | No paper in any pass ties Nesterov's increasing schedule β_k = (k−1)/(k+2) to drift or norm growth. |
| Nuclear-norm bound for linear networks under heavy ball | Not found | |
| Implicit bias experiment on diagonal networks | Known qualitatively | Papazov et al., AISTATS 2024, and Lyu, Zhang and Zheng, arXiv 2506.14806, show that heavy ball acts like a change of initialisation through the asymptotic balancedness. The paper presents the experiment as an illustration of the bounds. |
| Lean formalisation | Not found for this topic | `heavy-ball-lean` (Zenodo 20480592, June 2026) proves heavy ball linear convergence for strongly convex functions. Optlib (arXiv 2403.11437) formalises convergence of gradient methods, including Nesterov. Neither touches symmetries or conserved quantities. |

## Papers read in full text

Downloaded from arXiv on 13 October 2026 and searched passage by passage:

- Kunin et al., arXiv 2012.04728. Tanaka and Kunin, arXiv 2105.02716. Marcotte et al., arXiv 2307.00144 and 2405.12888 (Appendix N read in full). Marcotte et al., arXiv 2506.06194.
- Gluch and Urbanke, arXiv 2104.05508. Zhao et al., arXiv 2210.17216 (Appendix E). Ziyin et al., arXiv 2402.07193 (Appendix D). Le and Jegelka, arXiv 2201.11968 (no momentum, no drift).
- Papazov et al., arXiv 2403.05293. Lyu et al., AAAI 2025. Lyu, Zhang and Zheng, arXiv 2506.14806. Ghosh et al., arXiv 2302.00849. Kovachki and Stuart, arXiv 1906.04285. Farazmand, arXiv 1807.11354. Josz and Li, arXiv 2407.15044.
- Heo et al., arXiv 2006.08217. Wan et al., arXiv 2006.08419. Arora, Li and Lyu, arXiv 1812.03981. Li and Arora, arXiv 1910.07454. Kosson et al., arXiv 2305.17212 (weight-decay equilibrium, no overlap).
- Du, Hu and Lee, arXiv 1806.00900. Medeiros, arXiv 2604.07405 (no momentum). Singh, arXiv 2608.05136 (preconditioned flows only).
- Recent conservation-law papers, none of which treats momentum: Tran et al., arXiv 2606.17816; Galley, Shahverdi and Flinth, arXiv 2606.10913; Nguyen and Montúfar, arXiv 2609.34549 (numerical drift under GD only); the survey arXiv 2506.13018; arXiv 2512.21447 (Noether flow under SGD noise); arXiv 2511.01137.
- Acceleration background, none of which treats symmetries: Shi et al., arXiv 1810.08907; Wibisono, Wilson and Jordan, arXiv 1603.04245; arXiv 2201.08311; Zhang and Lin, arXiv 2605.18528 (scale-invariant optimisers such as Muon, a different sense of scale invariance).
- Lean: Optlib, arXiv 2403.11437; the `heavy-ball-lean` Zenodo record.

Not read: Attouch, Goudou and Redont (2000), which is not on arXiv. Josz and Li say it covers finite horizons only.

## What this means for the paper

The paper credits all of the overlaps above at the place where each result appears. The new content that survives every pass is the following:

- the uniform-in-time bounds for heavy ball and their sharpness, which answer the open observation in Marcotte et al. (2024, Appendix N);
- the exact discrete identity and bound for a general generator, where the case A = I is in Heo et al.;
- the exact identity for Nesterov's method with the gradient at the extrapolated point, and the dichotomy for positive semidefinite generators;
- the first-order term in the mass at infinite time;
- the nuclear-norm bound for linear networks;
- the Lean formalisation.

The strongest claim is the Nesterov dichotomy, and nothing in any pass came close to it. The weakest is the first-order formula, where only the passage to t = ∞ is new.
