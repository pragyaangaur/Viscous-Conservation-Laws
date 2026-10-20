# Viscosity ML

Gradient descent is the overdamped limit of a ball rolling through a viscous fluid, and momentum puts the mass back. This project asks what that friction does to the conservation laws that symmetries give a network, such as the balancedness of a ReLU neuron or the matrix W1 W1ᵀ − W2ᵀ W2 of a linear network. Momentum is known to destroy these laws exactly. We show that they survive approximately and that the ratio of inertia to friction controls how well.

The write-up is a preprint on Zenodo, archived with version 1.0.0 of this repository.

## Results

For heavy ball in continuous time, m θ'' + γ θ' = −∇L, a quadratic conserved quantity Q started at rest drifts by exactly (2m/γ) ∫ ⟨θ', Aθ'⟩ dt. The drift is bounded for all time by 2m‖A‖(L₀ − L∞)/γ², and this constant is attained for scale-invariant parameters.

In discrete time the identity is exact with weights (1 + β − 2β^(N−j))/(1 − β). The drift is at most (1+β)/(1−β) ‖A‖ times the total squared step length, and with a smoothness constant ℓ it is at most 2(1+β)η‖A‖(L₀ − L_N)/((1−β)(2(1−β) − ηℓ)). At fixed momentum it vanishes linearly in the step size, and the controlling quantity is η/(1−β)², which Papazov, Pesme and Flammarion found for diagonal linear networks in 2024.

For Nesterov's method with the gradient at the extrapolated point there is an exact identity: the one-step drift D_k obeys D_k = β_k D_{k−1} + β_k(1+β_k) Q(θ_k − θ_{k−1}) + s²⟨g_k, A g_k⟩. Under Nesterov's schedule β_k = (k−1)/(k+2) the resulting weights grow linearly. For positive semidefinite generators, which include scale-invariant weights before a normalisation layer, we prove that the drift stays above a positive constant that does not depend on the step size, while heavy ball's drift vanishes linearly in the step (figure in [paper/fig_dichotomy.png](paper/fig_dichotomy.png)). The proved constant is very conservative. For indefinite generators, such as the rescaling of a ReLU neuron, the dichotomy is only observed numerically.

As the mass goes to zero, (Q∞ − Q₀)/m tends to (2/γ³)∫⟨∇L, A∇L⟩ along gradient flow. This is proved when the trajectories stay in a bounded set, which Josz and Li's 2024 theorem reduces to boundedness of gradient flow, and when gradient flow reaches the infimum of the loss.

On a diagonal linear network the conserved quantities set the implicit bias, and the learned solution moves away from the gradient flow solution and becomes less sparse as the drift grows.

## What is proved, what is checked, and what is only observed

The Lean 4 project in [lean/](lean) builds on Mathlib with no `sorry`, and its main theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Parameters live in an arbitrary real inner product space, so the statements cover every architecture with a linear symmetry. It proves the discrete identities for any momentum schedule, the closed form and both bounds for constant momentum, the equality case for scale-invariant parameters, the Nesterov-schedule weights, the continuous heavy ball identity, energy identity and bound, the Nesterov ODE identities, the matrix law for linear networks (`LinearNet.lean`), the exact identity for Nesterov's method (`Nesterov.lean`), and the step-size independent lower bound for positive semidefinite generators (`NesterovLower.lean`).

Proved on paper only: the first-order formula in the mass and its lemma, the limits as T → ∞, the trace-to-nuclear-norm duality step, and the final choice of J in the dichotomy corollary. Numerical only: the dichotomy for indefinite generators and the convergence of the Nesterov drift to the ODE value.

The bounds hold in every run but are loose for typical initialisations, by factors between about 3 and 80, because the kinetic term has both signs. The discrete energy bound needs ηℓ < 2(1−β) with ℓ measured along the run, and this fails for η = 0.005, β = 0.97, where the bound does not apply.

## What is new and what is not

The differential identities under momentum are known in substance from Tanaka and Kunin (2021), Kunin et al. (2021) and, for Nesterov's ODE, Gluch and Urbanke (2021). The plain gradient descent case is in Ziyin et al. (2024), and the discrete identity for the squared norm of scale-invariant weights is Lemma 2.2 of Heo et al. (AdamP, 2021). The first-order formula in the mass follows formally from the slow-manifold expansion, so only its limit at infinite time is new. The paper credits each of these where it is used.

What was not found in the 29 papers read in full: the uniform-in-time bounds for heavy ball and their sharpness, which give a theory for the boundedness that Marcotte et al. (2024, Appendix N) observed in experiments and left open; the discrete identity and bound for a general generator; the exact identity for Nesterov's method and the dichotomy for positive semidefinite generators; the nuclear-norm bound; and the Lean formalisation. [NOVELTY.md](NOVELTY.md) gives the claim-by-claim table with the exact theorem or equation of each overlap.

## Running it

The numerics need numpy, scipy and matplotlib. Each script prints its table, and the saved outputs are the `results_*.txt` files next to them.

```bash
cd numerics && python3 exp_continuous.py
```

```bash
cd numerics && python3 exp_discrete.py
```

`exp_discrete.py` is slow because the Nesterov runs go to millions of iterations. `exp_nesterov_tail.py` tracks the Nesterov loss and drift over time, `exp_implicit_bias.py` is the diagonal network experiment, and `fig_dichotomy.py` redraws the figure from the numbers in `results_discrete.txt`, and `exp_nesterov_proof.py` checks the Nesterov identity, the dichotomy on a scale-invariant model and the explicit constant.

To check the proofs, fetch the Mathlib cache once and build.

```bash
cd lean && lake exe cache get && lake build
```

The paper itself is on Zenodo and is not kept in this repository.
