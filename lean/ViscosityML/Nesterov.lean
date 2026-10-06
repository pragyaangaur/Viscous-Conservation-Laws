import Mathlib
import ViscosityML.Discrete

/-!
# Nesterov's method with the gradient at the extrapolated point

`y 0 = θ 0`, `y (k+1) = θ (k+1) + β (k+1) (θ (k+1) - θ k)`, `θ (k+1) = y k - s g k`, and the
gradient `g k` at `y k` is orthogonal to the generator: `⟪g k, A (y k)⟫ = 0`.

Because `Q` is quadratic and `y` is an affine extrapolation, the one-step drift
`D k = Q (θ (k+1)) - Q (θ k)` obeys an exact linear recursion (`D_succ`)
`D (k+1) = β (k+1) D k + β (k+1) (1 + β (k+1)) Q (θ (k+1) - θ k) + s² ⟪g (k+1), A g (k+1)⟫`.

For Nesterov's schedule `β k = (k-1)/(k+2)` this gives the closed form
`Q (θ N) - Q (θ 0) = ∑ i < N, (1 + i/2 - i(i+1)(i+2)/(2N(N+1))) F i` (`drift_nag_nesterov`),
with `F` the forcing above. When `A` is positive semidefinite every term is nonnegative
(`drift_nag_ge`), and on the first half of the run the weight is at least `i/4`.
-/

open scoped RealInnerProductSpace
open Finset

namespace ViscosityML

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nesterov's method with momentum schedule `β` and step `s`. -/
structure NAG (A : E →L[ℝ] E) (β : ℕ → ℝ) (s : ℝ) (θ y g : ℕ → E) : Prop where
  symm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫
  orth : ∀ k, ⟪g k, A (y k)⟫ = 0
  extrap0 : y 0 = θ 0
  extrap : ∀ k, y (k + 1) = θ (k + 1) + β (k + 1) • (θ (k + 1) - θ k)
  step : ∀ k, θ (k + 1) = y k - s • g k

variable {A : E →L[ℝ] E} {β : ℕ → ℝ} {s : ℝ} {θ y g : ℕ → E}

/-- Polarisation for the quadratic form of a symmetric map. -/
lemma Q_add (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (a d : E) :
    Q A (a + d) = Q A a + 2 * ⟪a, A d⟫ + Q A d := by
  have : ⟪d, A a⟫ = ⟪a, A d⟫ := by rw [← hsymm, real_inner_comm]
  simp only [Q, map_add, inner_add_left, inner_add_right, this]; ring

lemma Q_smul (a : E) (c : ℝ) : Q A (c • a) = c ^ 2 * Q A a := by
  simp only [Q, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]; ring

/-- The exact extrapolation identity for a quadratic form. -/
lemma Q_extrap (hsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (a c : E) (b : ℝ) :
    Q A (a + b • (a - c)) = (1 + b) * Q A a - b * Q A c + b * (1 + b) * Q A (a - c) := by
  have hc : c = a + (-1 : ℝ) • (a - c) := by simp
  have h1 := Q_add hsymm a (b • (a - c))
  have h2 : Q A c = Q A a + 2 * ⟪a, A ((-1 : ℝ) • (a - c))⟫ + Q A ((-1 : ℝ) • (a - c)) := by
    conv_lhs => rw [hc]
    exact Q_add hsymm a _
  rw [h1, h2, Q_smul, Q_smul]
  simp only [map_smul, inner_smul_right]
  ring

/-- One gradient step from the extrapolated point. -/
lemma Q_step_nag (h : NAG A β s θ y g) (k : ℕ) :
    Q A (θ (k + 1)) = Q A (y k) + s ^ 2 * ⟪g k, A (g k)⟫ := by
  have hy : ⟪y k, A (g k)⟫ = 0 := by rw [← h.symm, real_inner_comm, h.orth k]
  rw [h.step, sub_eq_add_neg, Q_add h.symm, ← neg_smul, Q_smul]
  simp only [map_smul, inner_smul_right, hy, mul_zero, Q]
  ring

/-- The forcing term of the recursion. -/
def Fnag (A : E →L[ℝ] E) (β : ℕ → ℝ) (s : ℝ) (θ g : ℕ → E) : ℕ → ℝ
  | 0 => s ^ 2 * ⟪g 0, A (g 0)⟫
  | k + 1 => β (k + 1) * (1 + β (k + 1)) * Q A (θ (k + 1) - θ k) +
      s ^ 2 * ⟪g (k + 1), A (g (k + 1))⟫

/-- One-step drift. -/
def Dnag (A : E →L[ℝ] E) (θ : ℕ → E) (k : ℕ) : ℝ := Q A (θ (k + 1)) - Q A (θ k)

lemma D_zero (h : NAG A β s θ y g) : Dnag A θ 0 = Fnag A β s θ g 0 := by
  simp only [Dnag, Fnag, Q_step_nag h 0, h.extrap0]; ring

/-- The exact recursion for Nesterov's method. -/
theorem D_succ (h : NAG A β s θ y g) (k : ℕ) :
    Dnag A θ (k + 1) = β (k + 1) * Dnag A θ k + Fnag A β s θ g (k + 1) := by
  simp only [Dnag, Fnag]
  rw [Q_step_nag h (k + 1), h.extrap, Q_extrap h.symm]
  ring

theorem drift_nag_sum (θ : ℕ → E) (N : ℕ) :
    Q A (θ N) - Q A (θ 0) = ∑ k ∈ range N, Dnag A θ k := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ← ih]; simp only [Dnag]; ring

/-- Under Nesterov's schedule the one-step drift is an explicit average of past forcing. -/
lemma D_nest (h : NAG A nest s θ y g) (N : ℕ) :
    Dnag A θ N = Fnag A nest s θ g N + ∑ i ∈ range N,
      ((i : ℝ) * (i + 1) * (i + 2) / ((N : ℝ) * (N + 1) * (N + 2))) * Fnag A nest s θ g i := by
  induction N with
  | zero => simp [D_zero h]
  | succ n ih =>
    rw [D_succ h, ih, sum_range_succ]
    have hb : nest (n + 1) = (n : ℝ) / (n + 3) := by
      simp only [nest]; push_cast; ring_nf
    rw [hb, mul_add, mul_sum]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by positivity
      have hs : ∀ i ∈ range n, (n : ℝ) / (n + 3) *
          ((i : ℝ) * (i + 1) * (i + 2) / ((n : ℝ) * (n + 1) * (n + 2)) * Fnag A nest s θ g i)
          = (i : ℝ) * (i + 1) * (i + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2))
            * Fnag A nest s θ g i := by
        intro i _; field_simp; ring
      rw [sum_congr rfl hs]
      have hlast : (n : ℝ) / (n + 3) * Fnag A nest s θ g n =
          (n : ℝ) * (n + 1) * (n + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2))
            * Fnag A nest s θ g n := by
        congr 1; field_simp; ring
      rw [hlast]; ring

/-- Nesterov weights `1 + i/2 - i(i+1)(i+2)/(2N(N+1))`. -/
noncomputable def wNest (N i : ℕ) : ℝ :=
  1 + (i : ℝ) / 2 - (i : ℝ) * (i + 1) * (i + 2) / (2 * ((N : ℝ) * (N + 1)))

/-- Exact drift identity for Nesterov's method with Nesterov's schedule. -/
theorem drift_nag_nesterov (h : NAG A nest s θ y g) (N : ℕ) :
    Q A (θ N) - Q A (θ 0) = ∑ i ∈ range N, wNest N i * Fnag A nest s θ g i := by
  induction N with
  | zero => simp
  | succ n ih =>
    have key : Q A (θ (n + 1)) - Q A (θ 0) = (Q A (θ n) - Q A (θ 0)) + Dnag A θ n := by
      simp only [Dnag]; ring
    rw [key, ih, D_nest h, sum_range_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [wNest]
    · have hn' : (n : ℝ) ≠ 0 := by positivity
      have hs : ∀ i ∈ range n, wNest (n + 1) i * Fnag A nest s θ g i =
          wNest n i * Fnag A nest s θ g i +
            (i : ℝ) * (i + 1) * (i + 2) / ((n : ℝ) * (n + 1) * (n + 2)) * Fnag A nest s θ g i := by
        intro i _; simp only [wNest]; push_cast; field_simp; ring
      rw [sum_congr rfl hs, sum_add_distrib]
      have hlast : wNest (n + 1) n = 1 := by
        simp only [wNest]; push_cast; field_simp; ring
      rw [hlast]; ring

/-! ### Positivity for positive semidefinite generators -/

lemma nest_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ nest k := by
  simp only [nest]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply div_nonneg <;> linarith

lemma Fnag_nonneg (hpsd : ∀ x, 0 ≤ ⟪x, A x⟫) (k : ℕ) :
    0 ≤ Fnag A nest s θ g k := by
  cases k with
  | zero => simp only [Fnag]; exact mul_nonneg (sq_nonneg _) (hpsd _)
  | succ k =>
    simp only [Fnag]
    have hb := nest_nonneg (k := k + 1) (by omega)
    have : 0 ≤ Q A (θ (k + 1) - θ k) := hpsd _
    have : 0 ≤ ⟪g (k + 1), A (g (k + 1))⟫ := hpsd _
    positivity

lemma wNest_nonneg {N i : ℕ} (hi : i < N) : 0 ≤ wNest N i := by
  simp only [wNest]
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul hiN (by linarith : (i : ℝ) + 2 ≤ N + 1) (by positivity) (by positivity),
    mul_nonneg hi0 (mul_nonneg hi0 hi0)]

/-- On the first half of a run of length `N ≥ 6` the weight is at least `i/4`. -/
lemma wNest_ge {N i : ℕ} (hN : 6 ≤ N) (hi : 2 * i ≤ N) : (i : ℝ) / 4 ≤ wNest N i := by
  simp only [wNest]
  have hN' : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hi' : 2 * (i : ℝ) ≤ N := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hpos : (0 : ℝ) < 2 * ((N : ℝ) * (N + 1)) := by positivity
  have key : (i : ℝ) * (i + 1) * (i + 2) ≤ (1 + (i : ℝ) / 4) * (2 * ((N : ℝ) * (N + 1))) := by
    have h1 : ((i : ℝ) + 1) * (i + 2) ≤ ((N : ℝ) + 2) * (N + 4) / 4 := by nlinarith
    have h2 : ((N : ℝ) + 2) * (N + 4) ≤ 2 * (N * (N + 1)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hi0]
  have : (i : ℝ) * (i + 1) * (i + 2) / (2 * ((N : ℝ) * (N + 1))) ≤ 1 + (i : ℝ) / 4 := by
    rw [div_le_iff₀ hpos]; linarith
  linarith

/-- For a positive semidefinite generator the drift under Nesterov's method is at least the
contribution of any initial block of the first half of the run. -/
theorem drift_nag_ge (hpsd : ∀ x, 0 ≤ ⟪x, A x⟫) (h : NAG A nest s θ y g)
    {N M : ℕ} (hN : 6 ≤ N) (hM : 2 * M ≤ N) :
    ∑ i ∈ range M, (i : ℝ) / 4 * Fnag A nest s θ g i ≤ Q A (θ N) - Q A (θ 0) := by
  rw [drift_nag_nesterov h]
  have hMN : M ≤ N := by omega
  calc ∑ i ∈ range M, (i : ℝ) / 4 * Fnag A nest s θ g i
      ≤ ∑ i ∈ range M, wNest N i * Fnag A nest s θ g i := by
        refine sum_le_sum fun i hi => ?_
        have := mem_range.mp hi
        exact mul_le_mul_of_nonneg_right (wNest_ge hN (by omega)) (Fnag_nonneg hpsd i)
    _ ≤ ∑ i ∈ range N, wNest N i * Fnag A nest s θ g i := by
        refine sum_le_sum_of_subset_of_nonneg (range_mono hMN) fun i hi _ => ?_
        exact mul_nonneg (wNest_nonneg (mem_range.mp hi)) (Fnag_nonneg hpsd i)

end ViscosityML
