import Mathlib
import ViscosityML.Continuous

/-!
# Passages to infinite time and the sharp constant

These statements take the finite-time identities of `Continuous.lean` to the limit `T → ∞`.
They assume that the limits exist as hypotheses. For heavy ball the paper shows that the
limits exist under (H1) and (H2) of Theorem 3, which is not part of this file.

* `hb_limit_identity` : `γ (Qinf - Q 0) = 2m ∫₀^∞ ⟪v, A v⟫` for a motion started at rest
  (first identity of equation (hblim)).
* `hb_limit_bound` : `|Qinf - Q 0| ≤ 2m ‖A‖ (L 0 - Linf) / γ²` (second statement of (hblim)).
* `hb_sharp_finite`, `hb_sharp_limit` : for `A = id` the bound is an equality
  (Proposition 2).
* `nesterov_bound_finite` : finite-time bound on `[t₀, T]` for the Nesterov ODE with `r > 1`.
* `nesterov_identity_zero`, `nesterov_bound_zero` : the same from time `0`, for a motion that
  starts at rest.
* `nesterov_limit_identity` and `nesterov_limit_bound` : the limits `T → ∞` of Theorem 8,
  `Q∞ - Q 0 = 2/(r-1) ∫₀^∞ t K` and `|Q∞ - Q 0| ≤ 4‖A‖/(r-1)² ∫₀^∞ t (L - c)`.
-/

open scoped RealInnerProductSpace
open intervalIntegral Filter Topology MeasureTheory

namespace ViscosityML

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {θ v a G : ℝ → E} {m γ : ℝ}

/-- First identity of (hblim): the drift in the limit is `(2m/γ)` times the integral of `K`,
for a motion that starts at rest and has `P → 0`. -/
theorem hb_limit_identity {Qinf : ℝ}
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t) (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hrest : v 0 = 0)
    (hP : Tendsto (fun T => ⟪v T, A (θ T)⟫) atTop (𝓝 0))
    (hQ : Tendsto (fun T => Q A (θ T)) atTop (𝓝 Qinf))
    (hint : IntegrableOn (fun t => ⟪v t, A (v t)⟫) (Set.Ioi 0)) :
    γ * (Qinf - Q A (θ 0)) = 2 * m * ∫ t in Set.Ioi (0 : ℝ), ⟪v t, A (v t)⟫ := by
  have h1 : Tendsto (fun T => γ * (Q A (θ T) - Q A (θ 0)) +
      2 * m * (⟪v T, A (θ T)⟫ - ⟪v 0, A (θ 0)⟫)) atTop
      (𝓝 (γ * (Qinf - Q A (θ 0)) + 2 * m * (0 - ⟪v 0, A (θ 0)⟫))) :=
    ((hQ.sub_const _).const_mul γ).add ((hP.sub_const _).const_mul (2 * m))
  have h2 : Tendsto (fun T => 2 * m * ∫ t in (0 : ℝ)..T, ⟪v t, A (v t)⟫) atTop
      (𝓝 (2 * m * ∫ t in Set.Ioi (0 : ℝ), ⟪v t, A (v t)⟫)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul (2 * m)
  have h3 := tendsto_nhds_unique
    (h1.congr fun T => hb_identity hsymm hθ hv hode horth T) h2
  rw [hrest] at h3
  simpa using h3

/-- Second statement of (hblim): the uniform bound on the drift, for a motion that starts at
rest, with `v → 0`, `P → 0`, `Q → Qinf` and `L → Linf`. -/
theorem hb_limit_bound {Lf : ℝ → ℝ} {Qinf Linf : ℝ} (hm : 0 ≤ m) (hγ : 0 < γ)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t) (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hL : ∀ t, HasDerivAt Lf ⟪G t, v t⟫ t) (hrest : v 0 = 0)
    (hvT : Tendsto (fun T => ‖v T‖) atTop (𝓝 0))
    (hP : Tendsto (fun T => ⟪v T, A (θ T)⟫) atTop (𝓝 0))
    (hQ : Tendsto (fun T => Q A (θ T)) atTop (𝓝 Qinf))
    (hLf : Tendsto Lf atTop (𝓝 Linf)) :
    |Qinf - Q A (θ 0)| ≤ 2 * m * ‖A‖ * (Lf 0 - Linf) / γ ^ 2 := by
  have hlhs : Tendsto (fun T => |γ * (Q A (θ T) - Q A (θ 0)) +
      2 * m * (⟪v T, A (θ T)⟫ - ⟪v 0, A (θ 0)⟫)|) atTop
      (𝓝 |γ * (Qinf - Q A (θ 0)) + 2 * m * (0 - ⟪v 0, A (θ 0)⟫)|) :=
    (((hQ.sub_const _).const_mul γ).add ((hP.sub_const _).const_mul (2 * m))).abs
  have hv2 : Tendsto (fun T => ‖v T‖ ^ 2) atTop (𝓝 (0 ^ 2)) := hvT.pow 2
  have hE : Tendsto (fun T => m / 2 * ‖v T‖ ^ 2 + Lf T) atTop (𝓝 (m / 2 * 0 ^ 2 + Linf)) :=
    (hv2.const_mul (m / 2)).add hLf
  have hrhs : Tendsto (fun T => 2 * m * ‖A‖ *
      ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * ‖v T‖ ^ 2 + Lf T)) / γ) atTop
      (𝓝 (2 * m * ‖A‖ * ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * 0 ^ 2 + Linf)) / γ)) :=
    ((hE.const_sub _).const_mul _).div_const γ
  have hle := le_of_tendsto_of_tendsto hlhs hrhs (by
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact hb_drift_bound hm hγ hsymm hθ hv hode horth hL hT)
  rw [hrest] at hle
  simp only [inner_zero_left, norm_zero, sub_self, mul_zero, add_zero] at hle
  have e1 : |γ * (Qinf - Q A (θ 0))| = γ * |Qinf - Q A (θ 0)| := by
    rw [abs_mul, abs_of_pos hγ]
  rw [e1, le_div_iff₀ hγ] at hle
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hle]

/-- Proposition 2 at a finite time. For the identity generator, which is the scale-invariant
case, the bound of `hb_drift_bound` is an equality. -/
theorem hb_sharp_finite [Nontrivial E] {Lf : ℝ → ℝ} (hγ : γ ≠ 0)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t)
    (horth : ∀ t, ⟪G t, (ContinuousLinearMap.id ℝ E) (θ t)⟫ = 0)
    (hL : ∀ t, HasDerivAt Lf ⟪G t, v t⟫ t) (hrest : v 0 = 0) (T : ℝ) :
    γ * (‖θ T‖ ^ 2 - ‖θ 0‖ ^ 2) + 2 * m * ⟪v T, θ T⟫ =
      2 * m * ‖(ContinuousLinearMap.id ℝ E)‖ *
        ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * ‖v T‖ ^ 2 + Lf T)) / γ := by
  have hsymm : ∀ x y : E, ⟪(ContinuousLinearMap.id ℝ E) x, y⟫ =
      ⟪x, (ContinuousLinearMap.id ℝ E) y⟫ := fun _ _ => rfl
  have h1 := hb_identity hsymm hθ hv hode horth T
  have h2 := hb_energy hv hode hL T
  simp only [Q, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, hrest,
    inner_zero_left, sub_zero, mul_zero] at h1
  rw [ContinuousLinearMap.norm_id, mul_one, eq_div_iff hγ]
  linear_combination γ * h1 + 2 * m * h2

/-- Proposition 2 in the limit: for the identity generator the second statement of (hblim)
holds with equality, `‖θ∞‖² - ‖θ 0‖² = 2m (L 0 - L∞) / γ²`. -/
theorem hb_sharp_limit [Nontrivial E] {Lf : ℝ → ℝ} {Qinf Linf : ℝ} (hγ : γ ≠ 0)
    (hθ : ∀ t, HasDerivAt θ (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (hode : ∀ t, m • a t + γ • v t = -G t)
    (horth : ∀ t, ⟪G t, (ContinuousLinearMap.id ℝ E) (θ t)⟫ = 0)
    (hL : ∀ t, HasDerivAt Lf ⟪G t, v t⟫ t) (hrest : v 0 = 0)
    (hvT : Tendsto (fun T => ‖v T‖) atTop (𝓝 0))
    (hP : Tendsto (fun T => ⟪v T, θ T⟫) atTop (𝓝 0))
    (hQ : Tendsto (fun T => ‖θ T‖ ^ 2) atTop (𝓝 Qinf))
    (hLf : Tendsto Lf atTop (𝓝 Linf)) :
    Qinf - ‖θ 0‖ ^ 2 = 2 * m * (Lf 0 - Linf) / γ ^ 2 := by
  have hv2 : Tendsto (fun T => ‖v T‖ ^ 2) atTop (𝓝 (0 ^ 2)) := hvT.pow 2
  have hE : Tendsto (fun T => m / 2 * ‖v T‖ ^ 2 + Lf T) atTop (𝓝 (m / 2 * 0 ^ 2 + Linf)) :=
    (hv2.const_mul (m / 2)).add hLf
  have h1 : Tendsto (fun T => γ * (‖θ T‖ ^ 2 - ‖θ 0‖ ^ 2) + 2 * m * ⟪v T, θ T⟫) atTop
      (𝓝 (γ * (Qinf - ‖θ 0‖ ^ 2) + 2 * m * 0)) :=
    ((hQ.sub_const _).const_mul γ).add (hP.const_mul (2 * m))
  have h2 : Tendsto (fun T => 2 * m * ‖(ContinuousLinearMap.id ℝ E)‖ *
        ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * ‖v T‖ ^ 2 + Lf T)) / γ) atTop
      (𝓝 (2 * m * ‖(ContinuousLinearMap.id ℝ E)‖ *
        ((m / 2 * ‖v 0‖ ^ 2 + Lf 0) - (m / 2 * 0 ^ 2 + Linf)) / γ)) :=
    ((hE.const_sub _).const_mul _).div_const γ
  have h3 := tendsto_nhds_unique
    (h1.congr fun T => hb_sharp_finite hγ hθ hv hode horth hL hrest T) h2
  rw [hrest] at h3
  simp only [norm_zero, ContinuousLinearMap.norm_id, mul_zero, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_one] at h3
  rw [eq_div_iff (pow_ne_zero 2 hγ)]
  rw [eq_div_iff hγ] at h3
  linear_combination h3

/-! ### Nesterov ODE -/

section Nesterov

variable {r t₀ T : ℝ}

/-- Finite-time bound for the Nesterov ODE with `r > 1`. For every `c` below the loss on
`[t₀, T]`, the corrected quantity moves by at most
`2‖A‖/(r-1)² (2 ∫ t (L - c) + t₀² (E(t₀) - c))`. -/
theorem nesterov_bound_finite {Lf : ℝ → ℝ} (c : ℝ) (hr : 1 < r) (ht₀ : 0 < t₀) (hT : t₀ ≤ T)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθ : ∀ t ∈ Set.Icc t₀ T, HasDerivAt θ (v t) t)
    (hv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt v (a t) t)
    (hode : ∀ t ∈ Set.Icc t₀ T, a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hL : ∀ t ∈ Set.Icc t₀ T, HasDerivAt Lf ⟪G t, v t⟫ t)
    (hc : ∀ t ∈ Set.Icc t₀ T, c ≤ Lf t) :
    |(Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫) -
        (Q A (θ t₀) + 2 * t₀ / (r - 1) * ⟪v t₀, A (θ t₀)⟫)| ≤
      2 * ‖A‖ / (r - 1) ^ 2 *
        (2 * (∫ t in t₀..T, t * (Lf t - c)) + t₀ ^ 2 * (‖v t₀‖ ^ 2 / 2 + Lf t₀ - c)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hI : Set.uIcc t₀ T = Set.Icc t₀ T := Set.uIcc_of_le hT
  have hid := nesterov_identity hr.ne' ht₀ hT hsymm hθ hv hode horth
  have hen := nesterov_energy (Lf := Lf) c ht₀ hT hv hode hL
  have hcv : ContinuousOn v (Set.Icc t₀ T) := fun t ht =>
    (hv t ht).continuousAt.continuousWithinAt
  have hK : |∫ t in t₀..T, t * ⟪v t, A (v t)⟫| ≤ ‖A‖ * ∫ t in t₀..T, t * ‖v t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine (abs_integral_le_integral_abs hT).trans ?_
    have c1 : ContinuousOn (fun x => |x * ⟪v x, A (v x)⟫|) (Set.uIcc t₀ T) := by
      rw [hI]
      exact (continuousOn_id.mul (hcv.inner (A.continuous.comp_continuousOn hcv))).abs
    have c2 : ContinuousOn (fun x => ‖A‖ * (x * ‖v x‖ ^ 2)) (Set.uIcc t₀ T) := by
      rw [hI]
      exact continuousOn_const.mul (continuousOn_id.mul (hcv.norm.pow 2))
    refine integral_mono_on hT (c1.intervalIntegrable) (c2.intervalIntegrable)
      fun t ht => ?_
    have ht0 : 0 ≤ t := by linarith [ht.1]
    rw [abs_mul, abs_of_nonneg ht0]
    calc t * |⟪v t, A (v t)⟫| ≤ t * (‖A‖ * ‖v t‖ ^ 2) := by
          gcongr
          calc |⟪v t, A (v t)⟫| ≤ ‖v t‖ * ‖A (v t)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖v t‖ * (‖A‖ * ‖v t‖) := by gcongr; exact A.le_opNorm _
            _ = ‖A‖ * ‖v t‖ ^ 2 := by ring
      _ = ‖A‖ * (t * ‖v t‖ ^ 2) := by ring
  have hET : 0 ≤ T ^ 2 * (‖v T‖ ^ 2 / 2 + Lf T - c) := by
    have h1 := hc T ⟨hT, le_rfl⟩
    have h2 : 0 ≤ ‖v T‖ ^ 2 / 2 + Lf T - c := by nlinarith [sq_nonneg ‖v T‖]
    positivity
  have hkin : (r - 1) * ∫ t in t₀..T, t * ‖v t‖ ^ 2 ≤
      2 * (∫ t in t₀..T, t * (Lf t - c)) + t₀ ^ 2 * (‖v t₀‖ ^ 2 / 2 + Lf t₀ - c) := by
    linarith
  rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2 / (r - 1))]
  have hpos : 0 ≤ ∫ t in t₀..T, t * ‖v t‖ ^ 2 := by
    refine intervalIntegral.integral_nonneg hT fun t ht => ?_
    have : 0 ≤ t := by linarith [ht.1]
    positivity
  have h1 : 2 / (r - 1) * |∫ t in t₀..T, t * ⟪v t, A (v t)⟫| ≤
      2 / (r - 1) * (‖A‖ * ∫ t in t₀..T, t * ‖v t‖ ^ 2) := by gcongr
  refine h1.trans ?_
  have h2 : ∫ t in t₀..T, t * ‖v t‖ ^ 2 ≤
      (2 * (∫ t in t₀..T, t * (Lf t - c)) + t₀ ^ 2 * (‖v t₀‖ ^ 2 / 2 + Lf t₀ - c)) / (r - 1) := by
    rw [le_div_iff₀ hr1, mul_comm]; exact hkin
  calc 2 / (r - 1) * (‖A‖ * ∫ t in t₀..T, t * ‖v t‖ ^ 2)
      ≤ 2 / (r - 1) * (‖A‖ * ((2 * (∫ t in t₀..T, t * (Lf t - c)) +
          t₀ ^ 2 * (‖v t₀‖ ^ 2 / 2 + Lf t₀ - c)) / (r - 1))) := by gcongr
    _ = _ := by field_simp

/-- A function continuous on `[0, T]` has the right limit at `0`. -/
lemma tendsto_nhdsGT_of_continuousOn {g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (h : ContinuousOn g (Set.Icc 0 T)) : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
  ((h 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hT)).tendsto

/-- The integral from `t₀` to `T` tends to the integral from `0` to `T` as `t₀ → 0+`. -/
lemma tendsto_integral_lower {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (h : ContinuousOn f (Set.Icc 0 T)) :
    Tendsto (fun x => ∫ t in x..T, f t) (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have hI : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT.le
  have hint : IntegrableOn f (Set.uIcc 0 T) := by
    rw [hI]; exact h.integrableOn_Icc
  exact tendsto_nhdsGT_of_continuousOn (g := fun x => ∫ t in x..T, f t) hT
    (by simpa [hI] using intervalIntegral.continuousOn_primitive_interval_left hint)

/-- The Nesterov identity from time `0`, for a motion that starts at rest. The derivatives
exist for `t > 0` and `θ`, `v` are continuous on `[0, ∞)`. -/
theorem nesterov_identity_zero (hr : r ≠ 1) (hT : 0 < T)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθc : ContinuousOn θ (Set.Ici 0)) (hvc : ContinuousOn v (Set.Ici 0))
    (hθ : ∀ t, 0 < t → HasDerivAt θ (v t) t)
    (hv : ∀ t, 0 < t → HasDerivAt v (a t) t)
    (hode : ∀ t, 0 < t → a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0) (hrest : v 0 = 0) :
    (Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫) - Q A (θ 0) =
      2 / (r - 1) * ∫ t in (0 : ℝ)..T, t * ⟪v t, A (v t)⟫ := by
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Ici 0 := Set.Icc_subset_Ici_self
  have hθc' := hθc.mono hsub
  have hvc' := hvc.mono hsub
  have hAθ : ContinuousOn (fun t => A (θ t)) (Set.Icc 0 T) := A.continuous.comp_continuousOn hθc'
  have hAv : ContinuousOn (fun t => A (v t)) (Set.Icc 0 T) := A.continuous.comp_continuousOn hvc'
  have hQc : ContinuousOn (fun t => Q A (θ t)) (Set.Icc 0 T) := hθc'.inner hAθ
  have hR : ContinuousOn (fun t => Q A (θ t) + 2 * t / (r - 1) * ⟪v t, A (θ t)⟫)
      (Set.Icc 0 T) :=
    hQc.add (((continuousOn_const.mul continuousOn_id).div_const _).mul (hvc'.inner hAθ))
  have hf : ContinuousOn (fun t => t * ⟪v t, A (v t)⟫) (Set.Icc 0 T) :=
    continuousOn_id.mul (hvc'.inner hAv)
  have h1 := tendsto_nhdsGT_of_continuousOn hT hR
  have h2 := (tendsto_integral_lower hT hf).const_mul (2 / (r - 1))
  have h3 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioc 0 T := Ioc_mem_nhdsGT hT
  have h1' := (tendsto_const_nhds (x := Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫)).sub h1
  have key := tendsto_nhds_unique (h1'.congr' ?_) h2
  · rw [hrest] at key
    simpa using key
  · filter_upwards [h3] with x hx
    have := nesterov_identity hr hx.1 hx.2 hsymm
      (fun t ht => hθ t (lt_of_lt_of_le hx.1 ht.1))
      (fun t ht => hv t (lt_of_lt_of_le hx.1 ht.1))
      (fun t ht => hode t (lt_of_lt_of_le hx.1 ht.1)) horth
    exact this

/-- Finite-time bound from time `0` for the Nesterov ODE with `r > 1`, for a motion that
starts at rest and any `c` below the loss: `|R(T) - Q(0)| ≤ 4‖A‖/(r-1)² ∫₀ᵀ t (L - c)`. -/
theorem nesterov_bound_zero {Lf : ℝ → ℝ} (c : ℝ) (hr : 1 < r) (hT : 0 < T)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθc : ContinuousOn θ (Set.Ici 0)) (hvc : ContinuousOn v (Set.Ici 0))
    (hLc : ContinuousOn Lf (Set.Ici 0))
    (hθ : ∀ t, 0 < t → HasDerivAt θ (v t) t)
    (hv : ∀ t, 0 < t → HasDerivAt v (a t) t)
    (hode : ∀ t, 0 < t → a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hL : ∀ t, 0 < t → HasDerivAt Lf ⟪G t, v t⟫ t)
    (hc : ∀ t, 0 < t → c ≤ Lf t) (hrest : v 0 = 0) :
    |(Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫) - Q A (θ 0)| ≤
      4 * ‖A‖ / (r - 1) ^ 2 * ∫ t in (0 : ℝ)..T, t * (Lf t - c) := by
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Ici 0 := Set.Icc_subset_Ici_self
  have hθc' := hθc.mono hsub
  have hvc' := hvc.mono hsub
  have hLc' := hLc.mono hsub
  have hAθ : ContinuousOn (fun t => A (θ t)) (Set.Icc 0 T) := A.continuous.comp_continuousOn hθc'
  have hQc : ContinuousOn (fun t => Q A (θ t)) (Set.Icc 0 T) := hθc'.inner hAθ
  have hR : ContinuousOn (fun t => Q A (θ t) + 2 * t / (r - 1) * ⟪v t, A (θ t)⟫)
      (Set.Icc 0 T) :=
    hQc.add (((continuousOn_const.mul continuousOn_id).div_const _).mul (hvc'.inner hAθ))
  have hg : ContinuousOn (fun t => t ^ 2 * (‖v t‖ ^ 2 / 2 + Lf t - c)) (Set.Icc 0 T) :=
    (continuousOn_id.pow 2).mul (((hvc'.norm.pow 2).div_const 2).add hLc' |>.sub continuousOn_const)
  have hf : ContinuousOn (fun t => t * (Lf t - c)) (Set.Icc 0 T) :=
    continuousOn_id.mul (hLc'.sub continuousOn_const)
  have h1 := (tendsto_const_nhds (x := Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫)).sub
    (tendsto_nhdsGT_of_continuousOn hT hR)
  have h1' := h1.abs
  have h2 := tendsto_nhdsGT_of_continuousOn hT hg
  have h3 := tendsto_integral_lower hT hf
  have hrhs := (((h3.const_mul 2).add h2).const_mul (2 * ‖A‖ / (r - 1) ^ 2))
  have hle := le_of_tendsto_of_tendsto h1' hrhs (by
    filter_upwards [Ioc_mem_nhdsGT hT] with x hx
    exact nesterov_bound_finite c hr hx.1 hx.2 hsymm
      (fun t ht => hθ t (lt_of_lt_of_le hx.1 ht.1))
      (fun t ht => hv t (lt_of_lt_of_le hx.1 ht.1))
      (fun t ht => hode t (lt_of_lt_of_le hx.1 ht.1)) horth
      (fun t ht => hL t (lt_of_lt_of_le hx.1 ht.1))
      (fun t ht => hc t (lt_of_lt_of_le hx.1 ht.1)))
  simp only [hrest, inner_zero_left, mul_zero, add_zero, sub_zero, norm_zero] at hle
  refine hle.trans (le_of_eq ?_)
  simp
  ring

/-- Nesterov ODE, `T → ∞`: for a motion that starts at rest with `T P(T) → 0`,
`Q∞ - Q(0) = 2/(r-1) ∫₀^∞ t K`. -/
theorem nesterov_limit_identity {Qinf : ℝ} (hr : r ≠ 1)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθc : ContinuousOn θ (Set.Ici 0)) (hvc : ContinuousOn v (Set.Ici 0))
    (hθ : ∀ t, 0 < t → HasDerivAt θ (v t) t)
    (hv : ∀ t, 0 < t → HasDerivAt v (a t) t)
    (hode : ∀ t, 0 < t → a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0) (hrest : v 0 = 0)
    (hP : Tendsto (fun T => T * ⟪v T, A (θ T)⟫) atTop (𝓝 0))
    (hQ : Tendsto (fun T => Q A (θ T)) atTop (𝓝 Qinf))
    (hint : IntegrableOn (fun t => t * ⟪v t, A (v t)⟫) (Set.Ioi 0)) :
    Qinf - Q A (θ 0) = 2 / (r - 1) * ∫ t in Set.Ioi (0 : ℝ), t * ⟪v t, A (v t)⟫ := by
  have h1 : Tendsto (fun T => (Q A (θ T) + 2 / (r - 1) * (T * ⟪v T, A (θ T)⟫)) - Q A (θ 0))
      atTop (𝓝 ((Qinf + 2 / (r - 1) * 0) - Q A (θ 0))) :=
    (hQ.add (hP.const_mul _)).sub_const _
  have h2 : Tendsto (fun T => 2 / (r - 1) * ∫ t in (0 : ℝ)..T, t * ⟪v t, A (v t)⟫) atTop
      (𝓝 (2 / (r - 1) * ∫ t in Set.Ioi (0 : ℝ), t * ⟪v t, A (v t)⟫)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul _
  have h3 := tendsto_nhds_unique (h1.congr' (by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have := nesterov_identity_zero hr hT hsymm hθc hvc hθ hv hode horth hrest
    rw [← this]; ring)) h2
  simpa using h3

/-- Nesterov ODE, `T → ∞`, second bound of Theorem 8: for `r > 1`, a motion that starts at
rest, `T P(T) → 0` and any `c` below the loss,
`|Q∞ - Q(0)| ≤ 4‖A‖/(r-1)² ∫₀^∞ t (L - c)`. -/
theorem nesterov_limit_bound {Lf : ℝ → ℝ} {Qinf : ℝ} (c : ℝ) (hr : 1 < r)
    (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hθc : ContinuousOn θ (Set.Ici 0)) (hvc : ContinuousOn v (Set.Ici 0))
    (hLc : ContinuousOn Lf (Set.Ici 0))
    (hθ : ∀ t, 0 < t → HasDerivAt θ (v t) t)
    (hv : ∀ t, 0 < t → HasDerivAt v (a t) t)
    (hode : ∀ t, 0 < t → a t + (r / t) • v t = -G t)
    (horth : ∀ t, ⟪G t, A (θ t)⟫ = 0)
    (hL : ∀ t, 0 < t → HasDerivAt Lf ⟪G t, v t⟫ t)
    (hc : ∀ t, 0 < t → c ≤ Lf t) (hrest : v 0 = 0)
    (hP : Tendsto (fun T => T * ⟪v T, A (θ T)⟫) atTop (𝓝 0))
    (hQ : Tendsto (fun T => Q A (θ T)) atTop (𝓝 Qinf))
    (hint : IntegrableOn (fun t => t * (Lf t - c)) (Set.Ioi 0)) :
    |Qinf - Q A (θ 0)| ≤
      4 * ‖A‖ / (r - 1) ^ 2 * ∫ t in Set.Ioi (0 : ℝ), t * (Lf t - c) := by
  have h1 : Tendsto (fun T => |(Q A (θ T) + 2 * T / (r - 1) * ⟪v T, A (θ T)⟫) - Q A (θ 0)|)
      atTop (𝓝 |(Qinf + 2 / (r - 1) * 0) - Q A (θ 0)|) := by
    refine (((hQ.add (hP.const_mul (2 / (r - 1)))).sub_const _).abs).congr fun T => ?_
    ring_nf
  have h2 : Tendsto (fun T => 4 * ‖A‖ / (r - 1) ^ 2 * ∫ t in (0 : ℝ)..T, t * (Lf t - c)) atTop
      (𝓝 (4 * ‖A‖ / (r - 1) ^ 2 * ∫ t in Set.Ioi (0 : ℝ), t * (Lf t - c))) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul _
  have := le_of_tendsto_of_tendsto h1 h2 (by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact nesterov_bound_zero c hr hT hsymm hθc hvc hLc hθ hv hode horth hL hc hrest)
  simpa using this

end Nesterov

end ViscosityML
