import Mathlib
import ViscosityML.Nesterov

/-!
# A step-size independent lower bound for Nesterov's method

Let `A` be positive semidefinite (for example the identity on a block of scale-invariant
parameters) and run Nesterov's method with schedule `β k = (k-1)/(k+2)` and step `s`. Suppose
that on the ball of radius `ρ` around `θ 0` the gradient is bounded by `G` and satisfies
`‖∇L x - ∇L (θ 0)‖ ≤ H ‖x - θ 0‖`. Write `g₀ = ∇L (θ 0)` and `κ₀ = ⟪g₀, A g₀⟫`.

If `s G (J+2)² ≤ ρ` and `16 ‖A‖ ‖g₀‖ H G s (J+2)² ≤ κ₀`, then for every `N ≥ 6` with
`2 (J+2) ≤ N`
`Q (θ N) - Q (θ 0) ≥ (3 κ₀ s² / 512) ∑_{i=4}^{J+1} i³`   (`nesterov_lower_bound`).

Both conditions allow `J + 2` up to `τ / √s` for a `τ` that does not depend on `s`, and then
`s² ∑ i³ ≈ τ⁴ / 4`. So the drift stays bounded below as `s → 0`, while heavy ball with fixed
momentum has drift `O(s)` (`drift_bound_energy`).

The proof follows the early phase. While the iterates are near `θ 0` the gradient is close to
`g₀`, the velocity is close to `-s c_k g₀` with `c_k = (k+3)/4`, so `⟪v_k, A v_k⟫` is of order
`s² k² κ₀`, and the Nesterov weights multiply it by `k`.
-/

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace
open Finset

namespace ViscosityML

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {s : ℝ} {θ y g : ℕ → E}

/-- Step `v k = θ (k+1) - θ k`. -/
def vel (θ : ℕ → E) (k : ℕ) : E := θ (k + 1) - θ k

lemma vel_zero (h : NAG A nest s θ y g) : vel θ 0 = -(s • g 0) := by
  simp [vel, h.step 0, h.extrap0]

lemma vel_succ (h : NAG A nest s θ y g) (k : ℕ) :
    vel θ (k + 1) = nest (k + 1) • vel θ k - s • g (k + 1) := by
  simp only [vel]
  rw [h.step (k + 1), h.extrap k]
  abel

lemma nest_succ (k : ℕ) : nest (k + 1) = (k : ℝ) / (k + 3) := by
  simp only [nest]; push_cast; ring_nf

lemma nest_succ_nonneg (k : ℕ) : 0 ≤ nest (k + 1) := by
  rw [nest_succ]; positivity

lemma nest_succ_le_one (k : ℕ) : nest (k + 1) ≤ 1 := by
  rw [nest_succ, div_le_one (by positivity)]; linarith

lemma theta_sub_succ (k : ℕ) : θ (k + 1) - θ 0 = (θ k - θ 0) + vel θ k := by
  simp [vel]

lemma y_sub_succ (h : NAG A nest s θ y g) (k : ℕ) :
    y (k + 1) - θ 0 = (θ (k + 1) - θ 0) + nest (k + 1) • vel θ k := by
  rw [h.extrap k, vel]; abel

section bounds

variable (grad : E → E) {G H ρ : ℝ}

/-- Early-phase position and velocity bounds. -/
theorem early_bounds (h : NAG A nest s θ y g) (hg : ∀ k, g k = grad (y k)) (hs : 0 ≤ s)
    (hG0 : 0 ≤ G) (hGb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x‖ ≤ G) {J : ℕ}
    (hJ : s * G * ((J : ℝ) + 2) ^ 2 ≤ ρ) :
    ∀ k ≤ J, ‖θ k - θ 0‖ ≤ s * G * ((k : ℝ) + 1) ^ 2 ∧
      ‖y k - θ 0‖ ≤ s * G * ((k : ℝ) + 2) ^ 2 ∧ ‖vel θ k‖ ≤ s * G * ((k : ℝ) + 1) := by
  have hsG : 0 ≤ s * G := mul_nonneg hs hG0
  intro k
  induction k with
  | zero =>
    intro hk
    have hρ : 0 ≤ ρ := le_trans (by positivity) hJ
    have hy0 : ‖y 0 - θ 0‖ = 0 := by simp [h.extrap0]
    refine ⟨by simp; positivity, by rw [hy0]; positivity, ?_⟩
    rw [vel_zero h, norm_neg, norm_smul, Real.norm_of_nonneg hs, hg 0]
    have := hGb (y 0) (by rw [hy0]; exact hρ)
    push_cast; nlinarith
  | succ k ih =>
    intro hk
    obtain ⟨hT, hY, hV⟩ := ih (by omega)
    have hkJ : (k : ℝ) + 1 ≤ J := by exact_mod_cast hk
    have hT' : ‖θ (k + 1) - θ 0‖ ≤ s * G * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      rw [theta_sub_succ]
      refine (norm_add_le _ _).trans ?_
      push_cast; nlinarith
    have hY' : ‖y (k + 1) - θ 0‖ ≤ s * G * (((k + 1 : ℕ) : ℝ) + 2) ^ 2 := by
      rw [y_sub_succ h, ← (by push_cast; ring : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2)] at *
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (nest_succ_nonneg k)]
      have h1 : nest (k + 1) * ‖vel θ k‖ ≤ ‖vel θ k‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (nest_succ_le_one k)
      push_cast at hT' ⊢; nlinarith
    refine ⟨hT', hY', ?_⟩
    rw [vel_succ h]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (nest_succ_nonneg k), Real.norm_of_nonneg hs,
      hg (k + 1)]
    have hball : ‖y (k + 1) - θ 0‖ ≤ ρ := by
      refine hY'.trans (le_trans ?_ hJ)
      push_cast
      have : (k : ℝ) + 1 + 2 ≤ J + 2 := by linarith
      gcongr
    have h1 : nest (k + 1) * ‖vel θ k‖ ≤ ‖vel θ k‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (nest_succ_le_one k)
    have h2 := hGb _ hball
    push_cast; nlinarith

/-- The constant-gradient velocity profile `c 0 = 1`, `c k = (k+3)/4`. -/
noncomputable def cN (k : ℕ) : ℝ := if k = 0 then 1 else ((k : ℝ) + 3) / 4

lemma cN_succ (k : ℕ) : cN (k + 1) = nest (k + 1) * cN k + 1 := by
  rw [nest_succ]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num [cN]
  · have : k ≠ 0 := by omega
    simp only [cN, this, ite_false, Nat.succ_ne_zero]
    push_cast
    field_simp; ring

lemma cN_ge (k : ℕ) : ((k : ℝ) + 2) / 4 ≤ cN k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [cN]; norm_num
  · simp only [cN, show k ≠ 0 by omega, ↓reduceIte]; linarith

lemma cN_pos (k : ℕ) : 0 < cN k := lt_of_lt_of_le (by positivity) (cN_ge k)

/-- Deviation of the velocity from the constant-gradient profile. -/
noncomputable def err (grad : E → E) (θ : ℕ → E) (s : ℝ) (k : ℕ) : E :=
  vel θ k + (s * cN k) • grad (θ 0)

lemma err_zero (h : NAG A nest s θ y g) (hg : ∀ k, g k = grad (y k)) : err grad θ s 0 = 0 := by
  simp [err, vel_zero h, hg 0, h.extrap0, cN]

lemma err_succ (h : NAG A nest s θ y g) (hg : ∀ k, g k = grad (y k)) (k : ℕ) :
    err grad θ s (k + 1) =
      nest (k + 1) • err grad θ s k - s • (grad (y (k + 1)) - grad (θ 0)) := by
  simp only [err]
  rw [vel_succ h, cN_succ, hg (k + 1)]
  module

/-- The deviation grows at most like `s² H G k (k+2)²`. -/
theorem err_bound (h : NAG A nest s θ y g) (hg : ∀ k, g k = grad (y k)) (hs : 0 ≤ s)
    (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hGb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x‖ ≤ G)
    (hHb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x - grad (θ 0)‖ ≤ H * ‖x - θ 0‖) {J : ℕ}
    (hJ : s * G * ((J : ℝ) + 2) ^ 2 ≤ ρ) :
    ∀ k ≤ J, ‖err grad θ s k‖ ≤ s ^ 2 * H * G * k * ((k : ℝ) + 2) ^ 2 := by
  have hb := early_bounds grad h hg hs hG0 hGb hJ
  intro k
  induction k with
  | zero => intro _; simp [err_zero grad h hg]
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    obtain ⟨_, hY, _⟩ := hb (k + 1) hk
    have hkJ : (k : ℝ) + 1 ≤ J := by exact_mod_cast hk
    have hball : ‖y (k + 1) - θ 0‖ ≤ ρ := by
      refine hY.trans (le_trans ?_ hJ); push_cast; gcongr
    rw [err_succ grad h hg]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (nest_succ_nonneg k), Real.norm_of_nonneg hs]
    have h1 : nest (k + 1) * ‖err grad θ s k‖ ≤ ‖err grad θ s k‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (nest_succ_le_one k)
    have h2 : s * ‖grad (y (k + 1)) - grad (θ 0)‖ ≤ s * (H * (s * G * ((k : ℝ) + 3) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ((hHb _ hball).trans ?_) hs
      refine mul_le_mul_of_nonneg_left ?_ hH0
      convert hY using 2; push_cast; ring
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have h3 : (k : ℝ) * ((k : ℝ) + 2) ^ 2 + ((k : ℝ) + 3) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 3) ^ 2 := by
      nlinarith
    have hc : 0 ≤ s ^ 2 * H * G := by positivity
    push_cast
    calc nest (k + 1) * ‖err grad θ s k‖ + s * ‖grad (y (k + 1)) - grad (θ 0)‖
        ≤ s ^ 2 * H * G * k * ((k : ℝ) + 2) ^ 2 + s * (H * (s * G * ((k : ℝ) + 3) ^ 2)) := by
          linarith
      _ = s ^ 2 * H * G * ((k : ℝ) * ((k : ℝ) + 2) ^ 2 + ((k : ℝ) + 3) ^ 2) := by ring
      _ ≤ s ^ 2 * H * G * (((k : ℝ) + 1) * ((k : ℝ) + 3) ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = s ^ 2 * H * G * ((k : ℝ) + 1) * ((k : ℝ) + 1 + 2) ^ 2 := by ring

/-- In the early phase the kinetic term is at least `s² (k+2)² κ₀ / 32`. -/
theorem kinetic_lower (hpsd : ∀ x, 0 ≤ ⟪x, A x⟫) (h : NAG A nest s θ y g)
    (hg : ∀ k, g k = grad (y k)) (hs : 0 ≤ s)
    (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hGb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x‖ ≤ G)
    (hHb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x - grad (θ 0)‖ ≤ H * ‖x - θ 0‖) {J : ℕ}
    (hJ : s * G * ((J : ℝ) + 2) ^ 2 ≤ ρ)
    (hτ : 16 * ‖A‖ * ‖grad (θ 0)‖ * H * G * s * ((J : ℝ) + 2) ^ 2 ≤ ⟪grad (θ 0), A (grad (θ 0))⟫) :
    ∀ k ≤ J, s ^ 2 * ((k : ℝ) + 2) ^ 2 * ⟪grad (θ 0), A (grad (θ 0))⟫ / 32 ≤
      ⟪vel θ k, A (vel θ k)⟫ := by
  intro k hk
  set g0 := grad (θ 0)
  set κ := ⟪g0, A g0⟫
  set c := cN k
  set e := err grad θ s k
  have hκ : 0 ≤ κ := hpsd _
  have he := err_bound grad h hg hs hG0 hH0 hGb hHb hJ k hk
  have hv : vel θ k = e - (s * c) • g0 := by simp only [e, err, c, g0, add_sub_cancel_right]
  have hc4 := cN_ge k
  have hcpos := cN_pos k
  have hkJ : (k : ℝ) ≤ J := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  -- expand the quadratic form
  have hsymm : ∀ a b : E, ⟪a, A b⟫ = ⟪b, A a⟫ := by
    intro a b
    have := (h.symm a b)
    rw [real_inner_comm] at this
    rw [← this]
  have hexp : ⟪vel θ k, A (vel θ k)⟫ =
      ⟪e, A e⟫ - 2 * (s * c) * ⟪g0, A e⟫ + (s * c) ^ 2 * κ := by
    rw [hv]
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, hsymm e g0]
    ring
  have hcross : |⟪g0, A e⟫| ≤ ‖g0‖ * ‖A‖ * ‖e‖ := by
    calc |⟪g0, A e⟫| ≤ ‖g0‖ * ‖A e‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖g0‖ * (‖A‖ * ‖e‖) := by gcongr; exact A.le_opNorm _
      _ = ‖g0‖ * ‖A‖ * ‖e‖ := by ring
  have hee : 0 ≤ ⟪e, A e⟫ := hpsd e
  -- the cross term is at most half of the main term
  have hsmall : 2 * (s * c) * (‖g0‖ * ‖A‖ * ‖e‖) ≤ (s * c) ^ 2 * κ / 2 := by
    have hX : 0 ≤ ‖g0‖ * ‖A‖ := by positivity
    have step1 : ‖g0‖ * ‖A‖ * ‖e‖ ≤ ‖g0‖ * ‖A‖ * (s ^ 2 * H * G * ((k : ℝ) + 2) ^ 3) := by
      refine mul_le_mul_of_nonneg_left (he.trans ?_) hX
      have : s ^ 2 * H * G * k * ((k : ℝ) + 2) ^ 2 ≤ s ^ 2 * H * G * ((k : ℝ) + 2) * ((k : ℝ) + 2) ^ 2 := by
        have : 0 ≤ s ^ 2 * H * G := by positivity
        gcongr; linarith
      linarith [this, show s ^ 2 * H * G * ((k : ℝ) + 2) * ((k : ℝ) + 2) ^ 2 =
        s ^ 2 * H * G * ((k : ℝ) + 2) ^ 3 by ring]
    have step2 : 16 * ‖A‖ * ‖g0‖ * H * G * s * ((k : ℝ) + 2) ^ 2 ≤ κ := by
      refine le_trans ?_ hτ
      have : ((k : ℝ) + 2) ^ 2 ≤ ((J : ℝ) + 2) ^ 2 := by gcongr
      have : 0 ≤ 16 * ‖A‖ * ‖g0‖ * H * G * s := by positivity
      nlinarith
    -- combine: 2 s c ‖g0‖‖A‖ s² H G (k+2)³ ≤ s² c² κ / 2 using c ≥ (k+2)/4
    have hsc : 0 ≤ s * c := by positivity
    calc 2 * (s * c) * (‖g0‖ * ‖A‖ * ‖e‖)
        ≤ 2 * (s * c) * (‖g0‖ * ‖A‖ * (s ^ 2 * H * G * ((k : ℝ) + 2) ^ 3)) := by gcongr
      _ = (s * c) * s * ((k : ℝ) + 2) / 8 * (16 * ‖A‖ * ‖g0‖ * H * G * s * ((k : ℝ) + 2) ^ 2) := by
          ring
      _ ≤ (s * c) * s * ((k : ℝ) + 2) / 8 * κ := by gcongr
      _ ≤ (s * c) * s * (4 * c) / 8 * κ := by gcongr; linarith
      _ = (s * c) ^ 2 * κ / 2 := by ring
  have hmain : (s * c) ^ 2 * κ / 2 ≤ ⟪vel θ k, A (vel θ k)⟫ := by
    rw [hexp]
    have : 2 * (s * c) * ⟪g0, A e⟫ ≤ 2 * (s * c) * (‖g0‖ * ‖A‖ * ‖e‖) := by
      have hsc : 0 ≤ 2 * (s * c) := by positivity
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcross) hsc
    linarith
  refine le_trans ?_ hmain
  have : ((k : ℝ) + 2) ^ 2 / 16 ≤ c ^ 2 := by
    have h0 : 0 ≤ ((k : ℝ) + 2) / 4 := by positivity
    nlinarith
  calc s ^ 2 * ((k : ℝ) + 2) ^ 2 * κ / 32 = s ^ 2 * (((k : ℝ) + 2) ^ 2 / 16) * κ / 2 := by ring
    _ ≤ s ^ 2 * c ^ 2 * κ / 2 := by gcongr
    _ = (s * c) ^ 2 * κ / 2 := by ring

/-- **Step-size independent lower bound for Nesterov's method.** -/
theorem nesterov_lower_bound (hpsd : ∀ x, 0 ≤ ⟪x, A x⟫) (h : NAG A nest s θ y g)
    (hg : ∀ k, g k = grad (y k)) (hs : 0 ≤ s)
    (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hGb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x‖ ≤ G)
    (hHb : ∀ x, ‖x - θ 0‖ ≤ ρ → ‖grad x - grad (θ 0)‖ ≤ H * ‖x - θ 0‖) {J N : ℕ}
    (hJ : s * G * ((J : ℝ) + 2) ^ 2 ≤ ρ)
    (hτ : 16 * ‖A‖ * ‖grad (θ 0)‖ * H * G * s * ((J : ℝ) + 2) ^ 2 ≤ ⟪grad (θ 0), A (grad (θ 0))⟫)
    (hN : 6 ≤ N) (hJN : 2 * (J + 2) ≤ N) :
    3 * ⟪grad (θ 0), A (grad (θ 0))⟫ * s ^ 2 / 512 * ∑ i ∈ Ico 4 (J + 2), (i : ℝ) ^ 3 ≤
      Q A (θ N) - Q A (θ 0) := by
  set κ := ⟪grad (θ 0), A (grad (θ 0))⟫
  have hκ : 0 ≤ κ := hpsd _
  have hK := kinetic_lower grad hpsd h hg hs hG0 hH0 hGb hHb hJ hτ
  refine le_trans ?_ (drift_nag_ge hpsd h hN hJN)
  rw [mul_sum]
  calc ∑ i ∈ Ico 4 (J + 2), 3 * κ * s ^ 2 / 512 * (i : ℝ) ^ 3
      ≤ ∑ i ∈ Ico 4 (J + 2), (i : ℝ) / 4 * Fnag A nest s θ g i := by
        refine sum_le_sum fun i hi => ?_
        obtain ⟨hi4, hiJ⟩ := mem_Ico.mp hi
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hKk := hK k (by omega)
        have hnest : (3 : ℝ) / 4 ≤ nest (k + 1) * (1 + nest (k + 1)) := by
          have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (by omega : 3 ≤ k)
          have hb : (1 : ℝ) / 2 ≤ nest (k + 1) := by
            rw [nest_succ, le_div_iff₀ (by positivity)]; linarith
          nlinarith
        have hF : nest (k + 1) * (1 + nest (k + 1)) * Q A (θ (k + 1) - θ k) ≤ Fnag A nest s θ g (k + 1) := by
          simp only [Fnag]
          have : 0 ≤ s ^ 2 * ⟪g (k + 1), A (g (k + 1))⟫ := mul_nonneg (sq_nonneg _) (hpsd _)
          linarith
        have hQ : Q A (θ (k + 1) - θ k) = ⟪vel θ k, A (vel θ k)⟫ := rfl
        have hKpos : 0 ≤ ⟪vel θ k, A (vel θ k)⟫ := hpsd _
        have hk0 : (0 : ℝ) ≤ k := by positivity
        push_cast
        have hchain : 3 / 4 * (s ^ 2 * ((k : ℝ) + 2) ^ 2 * κ / 32) ≤ Fnag A nest s θ g (k + 1) := by
          calc 3 / 4 * (s ^ 2 * ((k : ℝ) + 2) ^ 2 * κ / 32)
              ≤ nest (k + 1) * (1 + nest (k + 1)) * ⟪vel θ k, A (vel θ k)⟫ := by
                apply mul_le_mul hnest hKk (by positivity)
                exact le_trans (by norm_num) hnest
            _ ≤ _ := by rw [← hQ]; exact hF
        have hcube : ((k : ℝ) + 1) ^ 3 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2 := by
          have : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := by gcongr; linarith
          nlinarith
        calc 3 * κ * s ^ 2 / 512 * ((k : ℝ) + 1) ^ 3
            ≤ 3 * κ * s ^ 2 / 512 * (((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2) := by gcongr
          _ = ((k : ℝ) + 1) / 4 * (3 / 4 * (s ^ 2 * ((k : ℝ) + 2) ^ 2 * κ / 32)) := by ring
          _ ≤ ((k : ℝ) + 1) / 4 * Fnag A nest s θ g (k + 1) := by gcongr
    _ ≤ ∑ i ∈ range (J + 2), (i : ℝ) / 4 * Fnag A nest s θ g i := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
        · intro i hi; simp only [mem_Ico] at hi; simp only [mem_range]; omega
        · exact mul_nonneg (by positivity) (Fnag_nonneg hpsd i)

end bounds

end ViscosityML
