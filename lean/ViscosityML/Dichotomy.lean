import Mathlib
import ViscosityML.NesterovLower

/-!
# The step-size free bound of Corollary 12

`ViscosityML.nesterov_lower_bound` bounds the drift below for a given `J`. This file makes
the final choice `J + 2 = ⌊τ / √s⌋` of the paper, which shows that for every step
`s ≤ τ² / 400` the drift is at least `3 κ₀ τ⁴ / 4096`, a bound that does not depend on `s`.

* `sum_cube_range` : `∑_{i<n} i³ = (n (n-1) / 2)²`.
* `nesterov_dichotomy` : Corollary 12.
-/

open scoped RealInnerProductSpace
open Finset

namespace ViscosityML

lemma sum_cube_range (n : ℕ) : ∑ i ∈ range n, (i : ℝ) ^ 3 = ((n : ℝ) * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_cube_Ico (J : ℕ) (hJ : 4 ≤ J + 2) :
    ∑ i ∈ Ico 4 (J + 2), (i : ℝ) ^ 3 = (((J : ℝ) + 1) * ((J : ℝ) + 2) / 2) ^ 2 - 36 := by
  rw [sum_Ico_eq_sub _ hJ, sum_cube_range, sum_cube_range]
  push_cast
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {s : ℝ} {θ y g : ℕ → E}
variable (grad : E → E) {G H ρ : ℝ}

/-- Corollary 12 (dichotomy). If `τ > 0` satisfies `G τ² ≤ ρ` and
`16 ‖A‖ ‖g₀‖ H G τ² ≤ κ₀`, then for every step `0 < s ≤ τ²/400` and every
`N ≥ 2 τ / √s` the drift of Nesterov's method is at least `3 κ₀ τ⁴ / 4096`. -/
theorem nesterov_dichotomy (hpsd : ∀ x, 0 ≤ ⟪x, A x⟫) (h : NAG A nest s θ y g)
    (hg : ∀ k, g k = grad (y k)) (hs : 0 < s)
    (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hGb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x‖ ≤ G)
    (hHb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x - grad (θ 0)‖ ≤ H * ‖x - θ 0‖)
    {τ : ℝ} (hτ : 0 < τ) (hτρ : G * τ ^ 2 ≤ ρ)
    (hτκ : 16 * ‖A‖ * ‖grad (θ 0)‖ * H * G * τ ^ 2 ≤ ⟪grad (θ 0), A (grad (θ 0))⟫)
    (hsτ : s ≤ τ ^ 2 / 400) {N : ℕ} (hN : 2 * τ / Real.sqrt s ≤ N) :
    3 * ⟪grad (θ 0), A (grad (θ 0))⟫ * τ ^ 4 / 4096 ≤ Q A (θ N) - Q A (θ 0) := by
  set κ := ⟪grad (θ 0), A (grad (θ 0))⟫ with hκdef
  have hκ : 0 ≤ κ := hpsd _
  set u := Real.sqrt s with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hs
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs.le
  have hu20 : u ≤ τ / 20 := by
    rw [hu]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith
  have hq : (20 : ℝ) ≤ τ / u := by rw [le_div_iff₀ hu0]; linarith
  set J2 := ⌊τ / u⌋₊ with hJ2
  have hJ2ge : (20 : ℝ) ≤ J2 := by
    have := Nat.le_floor hq
    exact_mod_cast this
  have hJ2le : (J2 : ℝ) ≤ τ / u := Nat.floor_le (by positivity)
  have hJ2gt : τ / u < J2 + 1 := Nat.lt_floor_add_one _
  obtain ⟨J, hJ⟩ : ∃ J, J2 = J + 2 := ⟨J2 - 2, by
    have : 20 ≤ J2 := by exact_mod_cast hJ2ge
    omega⟩
  have hJR : ((J : ℝ) + 2) = J2 := by rw [hJ]; push_cast; ring
  have hJu : u * ((J : ℝ) + 2) ≤ τ := by
    rw [hJR]; calc u * J2 ≤ u * (τ / u) := by gcongr
      _ = τ := by field_simp
  have hJs : s * ((J : ℝ) + 2) ^ 2 ≤ τ ^ 2 := by
    rw [← hu2]; nlinarith [hJu, mul_nonneg hu0.le (by positivity : (0:ℝ) ≤ (J:ℝ) + 2)]
  have hJ1 : s * G * ((J : ℝ) + 2) ^ 2 ≤ ρ := by
    calc s * G * ((J : ℝ) + 2) ^ 2 = G * (s * ((J : ℝ) + 2) ^ 2) := by ring
      _ ≤ G * τ ^ 2 := by gcongr
      _ ≤ ρ := hτρ
  have hJ2' : 16 * ‖A‖ * ‖grad (θ 0)‖ * H * G * s * ((J : ℝ) + 2) ^ 2 ≤ κ := by
    calc 16 * ‖A‖ * ‖grad (θ 0)‖ * H * G * s * ((J : ℝ) + 2) ^ 2
        = (16 * ‖A‖ * ‖grad (θ 0)‖ * H * G) * (s * ((J : ℝ) + 2) ^ 2) := by ring
      _ ≤ (16 * ‖A‖ * ‖grad (θ 0)‖ * H * G) * τ ^ 2 := by gcongr
      _ ≤ κ := hτκ
  have hNq : 2 * (τ / u) ≤ N := by
    have : 2 * τ / u = 2 * (τ / u) := by ring
    rwa [this] at hN
  have hN6 : 6 ≤ N := by
    have : (6 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hJN : 2 * (J + 2) ≤ N := by
    have : (2 * ((J : ℝ) + 2)) ≤ N := by
      rw [hJR]; linarith
    exact_mod_cast this
  have hmain := nesterov_lower_bound grad hpsd h hg hs.le hG0 hH0 hGb hHb hJ1 hJ2' hN6 hJN
  refine le_trans ?_ hmain
  have hJ4 : 4 ≤ J + 2 := by
    have : (20 : ℝ) ≤ (J : ℝ) + 2 := by rw [hJR]; exact hJ2ge
    have : (18 : ℝ) ≤ J := by linarith
    have : 18 ≤ J := by exact_mod_cast this
    omega
  rw [sum_cube_Ico J hJ4]
  set x : ℝ := (J : ℝ) + 1 with hx
  have hx0 : 0 ≤ x := by positivity
  have hux : 9 / 10 * τ ≤ u * x := by
    have h1 : τ < u * (J2 + 1) := by
      have := hJ2gt
      rw [div_lt_iff₀ hu0] at this
      linarith
    have h2 : (J2 : ℝ) = x + 1 := by rw [← hJR, hx]; ring
    rw [h2] at h1
    nlinarith
  have hsum : x ^ 4 / 4 - 36 ≤ (x * (x + 1) / 2) ^ 2 - 36 := by
    have : x ^ 4 / 4 ≤ (x * (x + 1) / 2) ^ 2 := by nlinarith [sq_nonneg x, mul_nonneg hx0 hx0]
    linarith
  have hxe : ((J : ℝ) + 1) * ((J : ℝ) + 2) / 2 = x * (x + 1) / 2 := by rw [hx]; ring
  rw [hxe]
  have hs2 : s ^ 2 = u ^ 4 := by rw [← hu2]; ring
  have hkey : τ ^ 4 / 8 ≤ s ^ 2 * ((x * (x + 1) / 2) ^ 2 - 36) := by
    rw [hs2]
    have h1 : u ^ 4 * (x ^ 4 / 4 - 36) ≤ u ^ 4 * ((x * (x + 1) / 2) ^ 2 - 36) := by gcongr
    refine le_trans ?_ h1
    have h2 : (9 / 10 * τ) ^ 4 ≤ (u * x) ^ 4 := by gcongr
    have h3 : u ^ 4 ≤ (τ / 20) ^ 4 := by gcongr
    have : u ^ 4 * (x ^ 4 / 4 - 36) = (u * x) ^ 4 / 4 - 36 * u ^ 4 := by ring
    rw [this]
    nlinarith [h2, h3, pow_pos hτ 4]
  calc 3 * κ * τ ^ 4 / 4096 = 3 * κ / 512 * (τ ^ 4 / 8) := by ring
    _ ≤ 3 * κ / 512 * (s ^ 2 * ((x * (x + 1) / 2) ^ 2 - 36)) := by gcongr
    _ = 3 * κ * s ^ 2 / 512 * ((x * (x + 1) / 2) ^ 2 - 36) := by ring

end ViscosityML
