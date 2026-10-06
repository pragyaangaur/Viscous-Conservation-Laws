import Mathlib
import ViscosityML.Discrete

/-!
# Continuous time: heavy ball and the Nesterov ODE

A trajectory `θ` with velocity `v` and acceleration `a` moves under a force `-G t`,
where `G t` is the gradient of the loss at `θ t`. The only property of `G` we use is
the symmetry orthogonality `⟪G t, A (θ t)⟫ = 0`, and for the energy statements the
chain rule `d/dt L(θ t) = ⟪G t, v t⟫`, given as `HasDerivAt Lf ⟪G t, v t⟫ t`.

Heavy ball `m a + γ v = -G`:
* `hb_corrected_deriv` : `Q + (2m/γ) ⟪v, A θ⟫` has derivative `(2m/γ) ⟪v, A v⟫`
  (stated multiplied by `γ`).
* `hb_identity` : the integrated form.
* `hb_energy` : `γ ∫ ‖v‖² = E 0 - E T` with `E = m/2 ‖v‖² + L`.
* `hb_drift_bound` : `|γ ΔQ + 2m ΔP| ≤ 2m ‖A‖ (E 0 - E T) / γ`.

Nesterov ODE `a + (r/t) v = -G` on `[t₀, T]`, `0 < t₀`, `r ≠ 1`:
* `nesterov_identity` : `Q + (2t/(r-1)) ⟪v, A θ⟫` changes by `(2/(r-1)) ∫ t ⟪v, A v⟫`.
* `nesterov_energy` : `(r-1) ∫ t ‖v‖² = 2 ∫ t (L - c) - T²(E T - c) + t₀²(E t₀ - c)`.
-/

open scoped RealInnerProductSpace
open intervalIntegral

namespace ViscosityML

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {θ v a G : ℝ → E}

lemma hasDerivAt_Q (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) {t : ℝ}
    (hθ : HasDerivAt θ (v t) t) :
    HasDerivAt (fun s => Q A (θ s)) (2 * ⟪v t, A (θ t)⟫) t := by
  have hAθ : HasDerivAt (fun s => A (θ s)) (A (v t)) t :=
    A.hasFDerivAt.comp_hasDerivAt t hθ
  have := hθ.inner ℝ hAθ
  refine this.congr_deriv ?_
  rw [← hsymm, real_inner_comm]; ring

lemma hasDerivAt_P {t : ℝ} (hθ : HasDerivAt θ (v t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => ⟪v s, A (θ s)⟫) (⟪v t, A (v t)⟫ + ⟪a t, A (θ t)⟫) t := by
  have hAθ : HasDerivAt (fun s => A (θ s)) (A (v t)) t :=
    A.hasFDerivAt.comp_hasDerivAt t hθ
  exact hv.inner ℝ hAθ

lemma hasDerivAt_sq {t : ℝ} (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => ‖v s‖ ^ 2) (2 * ⟪v t, a t⟫) t := by
  have := hv.inner ℝ hv
  simp only [real_inner_self_eq_norm_sq] at this
  refine this.congr_deriv ?_
  rw [real_inner_comm]; ring

lemma continuous_of_deriv (hv : ∀ t, HasDerivAt v (a t) t) : Continuous v :=
  continuous_iff_continuousAt.2 fun t => (hv t).continuousAt

/-! ### Heavy ball -/

section HeavyBall

variable {m γ : ℝ}

/-- The corrected invariant `γ Q + 2m P` has derivative `2m K`. -/
theorem hb_corrected_deriv (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t) (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0) (t : ℝ) :
    HasDerivAt (fun s => γ * Q A (θ s) + 2 * m * ⟪v s, A (θ s)⟫)
      (2 * m * ⟪v t, A (v t)⟫) t := by
  have h := ((hasDerivAt_Q hsymm (hθ t)).const_mul γ).add
    ((hasDerivAt_P (A := A) (hθ t) (hv t)).const_mul (2 * m))
  refine h.congr_deriv ?_
  have key : γ * ⟪v t, A (θ t)⟫ + m * ⟪a t, A (θ t)⟫ = 0 := by
    have := congrArg (fun w => ⟪w, A (θ t)⟫) (hode t)
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, horth t, neg_zero] at this
    linarith
  linear_combination 2 * key

/-- Integrated heavy ball identity:
`γ (Q(T) - Q(0)) + 2m (P(T) - P(0)) = 2m ∫₀ᵀ ⟪v, A v⟫`. -/
theorem hb_identity (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t) (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0) (T : ℝ) :
    γ * (Q A (θ T) - Q A (θ 0)) + 2 * m * (⟪v T, A (θ T)⟫ - ⟪v 0, A (θ 0)⟫) =
      2 * m * ∫ t in (0 : ℝ)..T, ⟪v t, A (v t)⟫ := by
  have hc : Continuous fun t => ⟪v t, A (v t)⟫ := by
    have := continuous_of_deriv hv
    fun_prop
  have := integral_eq_sub_of_hasDerivAt
    (fun t _ => hb_corrected_deriv hsymm hθ hv hode horth t)
    ((hc.intervalIntegrable 0 T).const_mul (2 * m))
  rw [intervalIntegral.integral_const_mul] at this
  linarith

/-- Energy dissipation for heavy ball: `γ ∫₀ᵀ ‖v‖² = E(0) - E(T)`. -/
theorem hb_energy {Lf : ℝ → ℝ}
    (hv : ∀ t, HasDerivAt v (a t) t) (hode : ∀ t, m • a t + γ • v t = -G t)
    (hL : ∀ t, HasDerivAt Lf ⟪G t, v t⟫ t) (T : ℝ) :
    γ * ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2 =
      (m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * ‖v T‖ ^ 2 + Lf T) := by
  have hd : ∀ t, HasDerivAt (fun s => m / 2 * ‖v s‖ ^ 2 + Lf s) (-(γ * ‖v t‖ ^ 2)) t := by
    intro t
    refine (((hasDerivAt_sq (hv t)).const_mul (m / 2)).add (hL t)).congr_deriv ?_
    have := congrArg (fun w => ⟪w, v t⟫) (hode t)
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left,
      real_inner_self_eq_norm_sq] at this
    rw [real_inner_comm (v t) (a t)] at this
    linear_combination this
  have hc : Continuous fun t => ‖v t‖ ^ 2 := by
    have := continuous_of_deriv hv; fun_prop
  have := integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((hc.intervalIntegrable 0 T).const_mul γ).neg)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at this
  linarith

/-- Uniform-in-time drift bound for heavy ball:
`|γ ΔQ + 2m ΔP| ≤ 2m ‖A‖ (E(0) - E(T)) / γ`. Starting at rest and with `v T → 0`, this
gives `|Q(∞) - Q(0)| ≤ 2m ‖A‖ (L(0) - L(∞)) / γ²`. -/
theorem hb_drift_bound {Lf : ℝ → ℝ} (hm : 0 ≤ m) (hγ : 0 < γ)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t) (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hL : ∀ t, HasDerivAt Lf ⟪G t, v t⟫ t) {T : ℝ} (hT : 0 ≤ T) :
    |γ * (Q A (θ T) - Q A (θ 0)) + 2 * m * (⟪v T, A (θ T)⟫ - ⟪v 0, A (θ 0)⟫)| ≤
      2 * m * ‖A‖ * ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * ‖v T‖ ^ 2 + Lf T)) / γ := by
  rw [hb_identity hsymm hθ hv hode horth T]
  have hcv := continuous_of_deriv hv
  have hK : |∫ t in (0 : ℝ)..T, ⟪v t, A (v t)⟫| ≤ ‖A‖ * ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine (abs_integral_le_integral_abs hT).trans ?_
    have c1 : Continuous fun x => |⟪v x, A (v x)⟫| := by fun_prop
    have c2 : Continuous fun x => ‖A‖ * ‖v x‖ ^ 2 := by fun_prop
    refine integral_mono_on hT (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)
      fun t _ => ?_
    calc |⟪v t, A (v t)⟫| ≤ ‖v t‖ * ‖A (v t)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v t‖ * (‖A‖ * ‖v t‖) := by gcongr; exact A.le_opNorm _
      _ = ‖A‖ * ‖v t‖ ^ 2 := by ring
  have hE := hb_energy hv hode hL T
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m), le_div_iff₀ hγ]
  calc 2 * m * |∫ t in (0 : ℝ)..T, ⟪v t, A (v t)⟫| * γ
      ≤ 2 * m * (‖A‖ * ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) * γ := by gcongr
    _ = 2 * m * ‖A‖ * (γ * ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) := by ring
    _ = _ := by rw [hE]

end HeavyBall

/-! ### Nesterov ODE -/

section Nesterov

variable {r t₀ T : ℝ}

/-- For the Nesterov ODE `a + (r/t) v = -G`, the corrected quantity
`Q + (2t/(r-1)) ⟪v, A θ⟫` has derivative `(2t/(r-1)) ⟪v, A v⟫`. -/
theorem nesterov_corrected_deriv (hr : r ≠ 1) (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    {t : ℝ} (ht : t ≠ 0) (hθ : HasDerivAt θ (v t) t) (hv : HasDerivAt v (a t) t)
    (hode : a t + (r / t) • v t = -G t) (horth : ⟪G t, A (θ t)⟫ = 0) :
    HasDerivAt (fun s => Q A (θ s) + 2 * s / (r - 1) * ⟪v s, A (θ s)⟫)
      (2 * t / (r - 1) * ⟪v t, A (v t)⟫) t := by
  have hr' : r - 1 ≠ 0 := sub_ne_zero.2 hr
  have hlin : HasDerivAt (fun s : ℝ => 2 * s / (r - 1)) (2 / (r - 1)) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).div_const (r - 1)
  have h := (hasDerivAt_Q hsymm hθ).add (hlin.mul (hasDerivAt_P (A := A) hθ hv))
  refine h.congr_deriv ?_
  have key : ⟪a t, A (θ t)⟫ = -(r / t) * ⟪v t, A (θ t)⟫ := by
    have := congrArg (fun w => ⟪w, A (θ t)⟫) hode
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, horth, neg_zero] at this
    linarith
  rw [key]
  field_simp
  ring

/-- Integrated Nesterov identity on `[t₀, T]` with `0 < t₀ ≤ T`. -/
theorem nesterov_identity (hr : r ≠ 1) (ht₀ : 0 < t₀) (hT : t₀ ≤ T)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t ∈ Set.Icc t₀ T, HasDerivAt θ (v t) t)
    (hv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt v (a t) t)
    (hode : ∀ t ∈ Set.Icc t₀ T, a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0) :
    (Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫) -
      (Q A (θ t₀) + 2 * t₀ / (r - 1) * ⟪v t₀, A (θ t₀)⟫) =
      2 / (r - 1) * ∫ t in t₀..T, t * ⟪v t, A (v t)⟫ := by
  have hI : Set.uIcc t₀ T = Set.Icc t₀ T := Set.uIcc_of_le hT
  have hcv : ContinuousOn v (Set.Icc t₀ T) := fun t ht =>
    (hv t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t => 2 * t / (r - 1) * ⟪v t, A (v t)⟫) (Set.uIcc t₀ T) := by
    rw [hI]
    exact (continuousOn_const.mul continuousOn_id |>.div_const _).mul
      (hcv.inner (A.continuous.comp_continuousOn hcv))
  have := integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [hI] at ht
      exact nesterov_corrected_deriv hr hsymm (by linarith [ht.1] : t ≠ 0)
        (hθ t ht) (hv t ht) (hode t ht) (horth t))
    (hcont.intervalIntegrable)
  rw [← this, ← intervalIntegral.integral_const_mul]
  refine integral_congr fun t _ => ?_
  ring

/-- Nesterov energy identity, valid without convexity:
`(r-1) ∫ t ‖v‖² = 2 ∫ t (L - c) - T²(E(T) - c) + t₀²(E(t₀) - c)`, `E = ‖v‖²/2 + L`. -/
theorem nesterov_energy {Lf : ℝ → ℝ} (c : ℝ) (ht₀ : 0 < t₀) (hT : t₀ ≤ T)
    (hv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt v (a t) t)
    (hode : ∀ t ∈ Set.Icc t₀ T, a t + (r / t) • v t = -G t)
    (hL : ∀ t ∈ Set.Icc t₀ T, HasDerivAt Lf ⟪G t, v t⟫ t) :
    (r - 1) * ∫ t in t₀..T, t * ‖v t‖ ^ 2 =
      2 * (∫ t in t₀..T, t * (Lf t - c)) - T ^ 2 * (‖v T‖ ^ 2 / 2 + Lf T - c) +
        t₀ ^ 2 * (‖v t₀‖ ^ 2 / 2 + Lf t₀ - c) := by
  have hI : Set.uIcc t₀ T = Set.Icc t₀ T := Set.uIcc_of_le hT
  have hd : ∀ t ∈ Set.uIcc t₀ T,
      HasDerivAt (fun s => s ^ 2 * (‖v s‖ ^ 2 / 2 + Lf s - c))
        (2 * t * (Lf t - c) - (r - 1) * (t * ‖v t‖ ^ 2)) t := by
    intro t ht
    rw [hI] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le ht₀ ht.1).ne'
    have hE : HasDerivAt (fun s => ‖v s‖ ^ 2 / 2 + Lf s - c)
        (⟪v t, a t⟫ + ⟪G t, v t⟫) t := by
      have := (((hasDerivAt_sq (hv t ht)).div_const 2).add (hL t ht)).sub_const c
      refine this.congr_deriv ?_; ring
    refine ((hasDerivAt_pow 2 t).mul hE).congr_deriv ?_
    have key : ⟪v t, a t⟫ + ⟪G t, v t⟫ = -(r / t) * ‖v t‖ ^ 2 := by
      have := congrArg (fun w => ⟪w, v t⟫) (hode t ht)
      simp only [inner_add_left, real_inner_smul_left, inner_neg_left,
        real_inner_self_eq_norm_sq] at this
      rw [real_inner_comm (v t) (a t)] at this
      linear_combination this
    rw [key]
    field_simp
    ring
  have hcv : ContinuousOn v (Set.Icc t₀ T) := fun t ht =>
    (hv t ht).continuousAt.continuousWithinAt
  have hcL : ContinuousOn Lf (Set.Icc t₀ T) := fun t ht =>
    (hL t ht).continuousAt.continuousWithinAt
  have i1 : IntervalIntegrable (fun t => t * (Lf t - c)) MeasureTheory.volume t₀ T := by
    apply ContinuousOn.intervalIntegrable; rw [hI]
    exact continuousOn_id.mul (hcL.sub continuousOn_const)
  have i2 : IntervalIntegrable (fun t => t * ‖v t‖ ^ 2) MeasureTheory.volume t₀ T := by
    apply ContinuousOn.intervalIntegrable; rw [hI]
    exact continuousOn_id.mul (hcv.norm.pow 2)
  have := integral_eq_sub_of_hasDerivAt hd
    (((i1.const_mul 2).sub (i2.const_mul (r - 1))).congr (by
      intro t _; ring))
  rw [intervalIntegral.integral_sub (by
      exact (i1.const_mul 2).congr (by intro t _; ring))
      (i2.const_mul (r - 1)),
    intervalIntegral.integral_const_mul] at this
  have h2 : ∫ t in t₀..T, 2 * t * (Lf t - c) = 2 * ∫ t in t₀..T, t * (Lf t - c) := by
    rw [← intervalIntegral.integral_const_mul]; refine integral_congr fun t _ => ?_
    ring
  rw [h2] at this
  linarith

end Nesterov

end ViscosityML
