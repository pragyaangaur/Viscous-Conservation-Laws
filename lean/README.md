# Lean 4 formalisation

This folder is a Lean 4 project for the identities and bounds of the paper. It depends on Physlib, which brings Mathlib with it, and it uses the toolchain `leanprover/lean4:v4.36.0`. It builds with no `sorry`.

```bash
cd lean && lake build
```

The first build needs the Mathlib cache that Physlib's `lake-manifest.json` pins. `lake exe cache get` fetches it. The command `lake env lean Axioms.lean` prints the axioms of the main theorems, and each of them uses only `propext`, `Classical.choice` and `Quot.sound`.

Parameters live in an arbitrary real inner product space `E`. The generator `A` is a continuous linear map that is symmetric, and the symmetry of the loss enters only through the orthogonality `⟪g, A θ⟫ = 0` of the gradient and the generator. In continuous time the trajectory and its velocity are differentiable functions with the stated derivatives, and the chain rule for the loss is a hypothesis.

## Files

| File | Content |
| --- | --- |
| `ViscosityML/Discrete.lean` | Discrete heavy ball: exact identities, bounds, Nesterov's schedule |
| `ViscosityML/Continuous.lean` | Heavy ball and Nesterov ODE: differential identities, energy, finite-time bounds |
| `ViscosityML/Limits.lean` | The limits T to infinity, the sharp constant, finite-time Nesterov bound |
| `ViscosityML/LinearNet.lean` | The matrix law of a two-layer linear network |
| `ViscosityML/Nesterov.lean` | The exact identity for Nesterov's method |
| `ViscosityML/NesterovLower.lean` | The step-size free lower bound for positive semidefinite generators |
| `ViscosityML/Dichotomy.lean` | The final choice of J in Corollary 12 |
| `ViscosityML/FirstOrder.lean` | Theorem 3, the first order formula in the mass, with the existence of the limits |
| `Axioms.lean` | Prints the axioms of the main theorems |

## Paper, Lean and numerics

The theorem numbers are those of the preprint, where all theorems, propositions, lemmas and corollaries share one counter. Equation labels are given by name. The numerical checks are in `../numerics/`, and the saved output of each is the `results_*.txt` file next to the script.

| Paper | Lean | Numerical check |
| --- | --- | --- |
| Setting: orthogonality of the gradient and the generator | `LinearNet.orth_of_factor` for losses `ℓ(W₂ W₁)`, a hypothesis elsewhere | `model.py` generators, residual checked implicitly by every identity |
| Theorem 1, `d/dt(γQ + 2mP) = 2mK` | `hb_corrected_deriv` | `exp_continuous.py` E1, column `dQ` against `(2m/γ) ∫K` |
| Theorem 1, integrated identity | `hb_identity` | `exp_continuous.py` E1 |
| Theorem 1, energy identity | `hb_energy` | Not checked separately |
| Theorem 1, bound (hbbound) at finite T | `hb_drift_bound` | `exp_continuous.py` E1, columns `bound` and `ratio` |
| Theorem 1, limit identity (hblim) | `hb_limit_identity` | `exp_continuous.py` E1 |
| Theorem 1, limit bound (hblim) | `hb_limit_bound` | `exp_continuous.py` E1 |
| Proposition 2, sharpness | `hb_sharp_finite`, `hb_sharp_limit` | `exp_continuous.py` E1c |
| Theorem 3, first order in the mass | `first_order_mass_full`, `first_order_mass`, with `Traj.vel_bound`, `Traj.dist_flow_le`, `Traj.l2_le`, `Traj.K_integral_diff`, `Traj.gap_finite`, `Traj.gap_infinite`, `Traj.P_tendsto`, `Traj.Q_tendsto` | `exp_continuous.py` E1 column `dQ/m` and E1b |
| Lemma 4 | Not in Lean, and the Lean proof of Theorem 3 does not use it | None |
| Theorem 5, step identity and recursion | `Q_step`, `P_zero`, `P_succ`, `drift_eq_sum` | `exp_discrete.py` D1 |
| Theorem 5, identity (discid) | `P_const`, `drift_const` | `exp_discrete.py` D1 and D2, `drift_scale_invariant` for `A = I` |
| Theorem 6, first bound | `abs_K_le`, `drift_bound_const` | `exp_discrete.py` D1 column `b1` |
| Theorem 6, energy bound | `sum_sq_le_of_descent`, `drift_bound_energy` | `exp_discrete.py` D1 column `b2` |
| Corollary 7, matrix identity | `LinearNet.C_step`, `LinearNet.P_succ`, `LinearNet.drift_matrix_const`, `LinearNet.quad_drift` | `check_exact_identities.py` C2 |
| Corollary 7, nuclear norm bound | `LinearNet.trace_drift_bound` for every test matrix `X` | `exp_discrete.py` D4 |
| Theorem 8, differential and integrated identity | `nesterov_corrected_deriv`, `nesterov_identity` | `exp_continuous.py` E2 |
| Theorem 8, energy identity | `nesterov_energy` | `exp_continuous.py` E2 |
| Theorem 8, limit identity and last bound | `nesterov_bound_finite`, `nesterov_identity_zero`, `nesterov_bound_zero`, `nesterov_limit_identity`, `nesterov_limit_bound` | `exp_continuous.py` E2 |
| Theorem 9, Nesterov's schedule | `P_nest`, `drift_nesterov_schedule` | `check_exact_identities.py` C1 |
| Theorem 10, exact identity for Nesterov's method | `Q_extrap`, `D_succ`, `drift_nag_sum`, `drift_nag_nesterov` | `exp_nesterov_proof.py` N1, `check_exact_identities.py` C3 |
| Theorem 11, lower bound | `Fnag_nonneg`, `wNest_nonneg`, `wNest_ge`, `drift_nag_ge`, `early_bounds`, `err_bound`, `kinetic_lower`, `nesterov_lower_bound` | `exp_nesterov_proof.py` N2 and N3 |
| Corollary 12, dichotomy | `sum_cube_Ico`, `nesterov_dichotomy` | `exp_nesterov_proof.py` N2 and N3 |
| Observation 13, indefinite generators | Not in Lean, open | `exp_discrete.py` D3, `exp_nesterov_tail.py` |
| Implicit bias table | Not in Lean | `exp_implicit_bias.py` |

## Differences between the paper, the Lean statements and the checks

* In `Limits.lean` the limits `T → ∞` of the finite identities take the existence of the limits as hypotheses (`Q` converges, `P → 0`, the integral converges). `FirstOrder.lean` proves these existence statements for heavy ball under (H1) (`Traj.integrable_K`, `Traj.P_tendsto`, `Traj.Q_tendsto`).
* The Lean proof of Theorem 3 follows a different route from the paper. The paper uses Lemma 4 and the Cauchy-Schwarz inequality. Lean bounds the mean square distance of the velocities by an energy identity for `v + F(φ)/γ` and then uses `x ≤ (x²/√m + √m)/2`, so the finite horizon error it proves is of order `√m`. The limit statement is the same. Lemma 4 is left out of Lean because the proof does not need it.
* The paper shows that `P → 0` by boundedness of `θ` and uniform continuity. Lean shows it from the equation `P' = K - (γ/m) P` and the integrability of `K`, which needs no boundedness of `θ`.
* The Lean version of (H1) asks for a convex set `B` that contains the trajectories, a bound `G` and a Lipschitz constant `H > 0` for the gradient on `B`. Compactness of `B` is not used. The trajectories solve the equations for `t ≥ 0` with two-sided derivatives at `0`, and `L` has gradient `F` everywhere, with `L ≥ Lstar` for the infimum.
* The continuous results are stated for functions `θ`, `v`, `a`, `G` with `HasDerivAt` hypotheses. The paper writes `G = ∇L(θ)`. The chain rule `d/dt L(θ) = ⟪G, v⟫` is a hypothesis of the energy statements.
* The Nesterov ODE bound is proved from time `0` under continuity of `θ`, `v` and `L` on `[0, ∞)` and `v 0 = 0`. The paper says only that the motion starts at rest.
* The constants `G` and `H` in `exp_nesterov_proof.py` N3 are estimated from 4000 random pairs of points, so the printed constant `7.2e-7` is an estimate of what Corollary 12 guarantees. Lean takes `G` and `H` as given hypotheses.
* The nuclear norm bound of Corollary 7 is checked numerically with the actual nuclear norm. In Lean it is the statement for every test matrix `X` with `|xᵀ X x| ≤ xᵀ x`.
