# Viscosity ML

Started 6 October 2026. The question was whether gradient descent being the overdamped limit of motion through a viscous fluid leads anywhere new. It led to exact drift identities and bounds for symmetry-induced conservation laws under heavy ball and Nesterov momentum. Read [README.md](README.md) first and [paper/main.pdf](paper/main.pdf) for the full argument.

## State on 6 October 2026

Two rounds of work on 6 October. The second round added the novelty check in [NOVELTY.md](NOVELTY.md), a proof of the first-order formula in the mass, an exact identity for Nesterov's method, a proof of the step-size dichotomy for positive semidefinite generators, and Lean proofs of the matrix law and of the Nesterov results. The paper draft, the Lean proofs and the numerics are consistent with each other. The repository has been public at github.com/pragyaangaur/Viscous-Conservation-Laws since 6 October 2026. The paper has not been posted to arXiv. The `.lake/` folder is ignored by git. The Lean project's `.lake/packages` was copied from `Mathematics/Principia Math/PolyhexHull` at the same Mathlib revision, with the prebuilt cache fetched by `lake exe cache get`. A full `lake build` takes several minutes.

## Where the novelty sits

The differential identity for Q under momentum is known in substance from Tanaka and Kunin (NeurIPS 2021) and Kunin et al. (ICLR 2021), and the paper credits them. What was not found in prior work: the uniform energy bounds and their sharpness, the exact discrete weights, the Nesterov identity and dichotomy, the first-order formula, the nuclear-norm bound and the formalisation. See NOVELTY.md for the claim-by-claim table.

## Traps

- The Nesterov dichotomy is a theorem only for positive semidefinite generators (Theorem 11 and Corollary 12). For indefinite ones, including ReLU rescaling, it is still a numerical observation. The proved constant is about seven orders of magnitude below the observed drift.
- An early run suggested the Nesterov drift diverges logarithmically on the ReLU net. `exp_nesterov_tail.py` showed it does not: at each fixed step the drift settles and the loss decays faster than t⁻². The growth as the step shrinks is slow convergence to the ODE value.
- ReLU kinks make adaptive ODE solvers crawl. The continuous-time checks use the smooth linear network for that reason, and the ReLU checks are done in discrete time.
- The first-order formula in the mass (Theorem 3) is proved on paper under hypotheses (H1) and (H2) but is not in Lean, and it gives no rate.
- The bounds are loose in typical runs. Do not claim they are tight except in the scale-invariant equality case.

## Next steps

1. Prove the dichotomy for indefinite generators, which needs uniform-in-time control of the discrete method against the Nesterov ODE. The high-resolution ODE of Shi, Du, Jordan and Su is the likely route.
2. Formalise Theorem 3 and the T → ∞ limits, which needs Grönwall and variation of constants in Mathlib.
3. Extend the implicit bias experiment to several problems and initialisation scales.
4. Redo the novelty search more widely before any submission.
