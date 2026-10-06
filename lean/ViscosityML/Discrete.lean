import Mathlib

/-!
# Drift of symmetry invariants under discrete heavy ball

Parameters `θ k` live in a real inner product space `E`. A continuous linear map `A`
is symmetric and generates a symmetry of the loss, which we only use through the
orthogonality `⟪g k, A (θ k)⟫ = 0` between the gradient and the generator. The
quadratic quantity `Q θ = ⟪θ, A θ⟫` is then conserved by gradient flow.

Heavy ball with momentum schedule `β` and step `η` is
`v 0 = -η g 0`, `v (k+1) = β (k+1) v k - η g (k+1)`, `θ (k+1) = θ k + v k`.

Main results:
* `drift_eq_sum` : `Q (θ N) - Q (θ 0) = ∑ k < N, (2 P k + K k)` with the exact
  recursion `P (k+1) = β (k+1) (P k + K k)`.
* `drift_const` : for constant `β`, `(1-β)(Q (θ N) - Q (θ 0)) = ∑ j < N, (1+β-2β^(N-j)) K j`.
* `drift_bound_const` : `|Q (θ N) - Q (θ 0)| ≤ (1+β)/(1-β) ‖A‖ ∑ j < N, ‖v j‖²`.
* `sum_sq_le_of_descent` and `drift_bound_energy` : with the descent inequality of an
  `ℓ`-smooth loss and `c = (1-β)/η - ℓ/2 > 0`,
  `|Q (θ N) - Q (θ 0)| ≤ (1+β)/(1-β) ‖A‖ (L (θ 0) - L (θ N)) / c`.
* `drift_scale_invariant` : the equality case for scale-invariant parameters.
* `drift_nesterov_schedule` : for `β k = (k-1)/(k+2)` the exact weights are
  `(j+1) - j(j+1)(j+2)/(N(N+1))`, which grow without bound in `j`.
-/

open scoped RealInnerProductSpace
open Finset

namespace ViscosityML

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symmetry quantity `Q θ = ⟪θ, A θ⟫`. -/
def Q (A : E →L[ℝ] E) (θ : E) : ℝ := ⟪θ, A θ⟫

/-- Hypotheses shared by every result: heavy ball iterates with a symmetric generator
orthogonal to the gradient. -/
structure HeavyBall (A : E →L[ℝ] E) (β : ℕ → ℝ) (η : ℝ) (θ v g : ℕ → E) : Prop where
  symm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫
  orth : ∀ k, ⟪g k, A (θ k)⟫ = 0
  pos : ∀ k, θ (k + 1) = θ k + v k
  vel0 : v 0 = -(η • g 0)
  vel : ∀ k, v (k + 1) = β (k + 1) • v k - η • g (k + 1)

variable {A : E →L[ℝ] E} {β : ℕ → ℝ} {η : ℝ} {θ v g : ℕ → E}

/-- Cross term `P k = ⟪v k, A (θ k)⟫`. -/
def P (A : E →L[ℝ] E) (θ v : ℕ → E) (k : ℕ) : ℝ := ⟪v k, A (θ k)⟫

/-- Kinetic term `K k = ⟪v k, A (v k)⟫`. -/
def K (A : E →L[ℝ] E) (v : ℕ → E) (k : ℕ) : ℝ := ⟪v k, A (v k)⟫

lemma Q_step (h : HeavyBall A β η θ v g) (k : ℕ) :
    Q A (θ (k + 1)) - Q A (θ k) = 2 * P A θ v k + K A v k := by
  have hs : ⟪θ k, A (v k)⟫ = ⟪v k, A (θ k)⟫ := by
    rw [← h.symm, real_inner_comm]
  simp only [Q, P, K, h.pos, map_add, inner_add_left, inner_add_right]
  rw [hs]; ring

lemma P_zero (h : HeavyBall A β η θ v g) : P A θ v 0 = 0 := by
  simp [P, h.vel0, inner_neg_left, inner_smul_left, h.orth 0]

lemma P_succ (h : HeavyBall A β η θ v g) (k : ℕ) :
    P A θ v (k + 1) = β (k + 1) * (P A θ v k + K A v k) := by
  simp only [P, K, h.vel, h.pos, inner_sub_left, inner_smul_left]
  have : ⟪v k, A (θ (k + 1))⟫ = ⟪v k, A (θ k)⟫ + ⟪v k, A (v k)⟫ := by
    rw [h.pos, map_add, inner_add_right]
  rw [← h.pos, this]; simp [h.orth (k + 1)]

/-- Exact telescoping form of the drift. -/
theorem drift_eq_sum (h : HeavyBall A β η θ v g) (N : ℕ) :
    Q A (θ N) - Q A (θ 0) = ∑ k ∈ range N, (2 * P A θ v k + K A v k) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ← ih, ← Q_step h n]; ring

/-- For constant momentum the cross term is a geometric sum of past kinetic terms. -/
lemma P_const (b : ℝ) (h : HeavyBall A (fun _ => b) η θ v g) (N : ℕ) :
    P A θ v N = ∑ j ∈ range N, b ^ (N - j) * K A v j := by
  induction N with
  | zero => simp [P_zero h]
  | succ n ih =>
    rw [P_succ h, ih, sum_range_succ, mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have : n + 1 - j = (n - j) + 1 := by
        have := mem_range.mp hj; omega
      rw [this, pow_succ]; ring
    · simp

/-- Exact drift identity for constant momentum, multiplied through by `1 - β`. -/
theorem drift_const (b : ℝ) (h : HeavyBall A (fun _ => b) η θ v g) (N : ℕ) :
    (1 - b) * (Q A (θ N) - Q A (θ 0)) =
      ∑ j ∈ range N, (1 + b - 2 * b ^ (N - j)) * K A v j := by
  induction N with
  | zero => simp
  | succ n ih =>
    have step := Q_step h n
    have hP := P_const b h n
    have key : Q A (θ (n + 1)) - Q A (θ 0) =
        (Q A (θ n) - Q A (θ 0)) + (2 * P A θ v n + K A v n) := by linarith
    rw [key, mul_add, ih, hP, sum_range_succ]
    simp only [Nat.add_sub_cancel_left]
    have hsplit : ∀ j ∈ range n, (1 + b - 2 * b ^ (n + 1 - j)) * K A v j =
        (1 + b - 2 * b ^ (n - j)) * K A v j + 2 * (1 - b) * (b ^ (n - j) * K A v j) := by
      intro j hj
      have : n + 1 - j = (n - j) + 1 := by have := mem_range.mp hj; omega
      rw [this, pow_succ]; ring
    rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum]
    ring

lemma abs_K_le (A : E →L[ℝ] E) (v : ℕ → E) (k : ℕ) : |K A v k| ≤ ‖A‖ * ‖v k‖ ^ 2 := by
  calc |K A v k| ≤ ‖v k‖ * ‖A (v k)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v k‖ * (‖A‖ * ‖v k‖) := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ * ‖v k‖ ^ 2 := by ring

/-- Uniform-in-time drift bound for constant momentum `0 ≤ β < 1`. -/
theorem drift_bound_const (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (h : HeavyBall A (fun _ => b) η θ v g) (N : ℕ) :
    |Q A (θ N) - Q A (θ 0)| ≤ (1 + b) / (1 - b) * (‖A‖ * ∑ j ∈ range N, ‖v j‖ ^ 2) := by
  have h1b : 0 < 1 - b := by linarith
  have hw : ∀ j ∈ range N, |1 + b - 2 * b ^ (N - j)| ≤ 1 + b := by
    intro j _
    have h0 : 0 ≤ b ^ (N - j) := pow_nonneg hb0 _
    have h1 : b ^ (N - j) ≤ 1 := pow_le_one₀ hb0 hb1.le
    rw [abs_le]; constructor <;> linarith
  have main : |(1 - b) * (Q A (θ N) - Q A (θ 0))| ≤ (1 + b) * (‖A‖ * ∑ j ∈ range N, ‖v j‖ ^ 2) := by
    rw [drift_const b h N]
    calc |∑ j ∈ range N, (1 + b - 2 * b ^ (N - j)) * K A v j|
        ≤ ∑ j ∈ range N, |(1 + b - 2 * b ^ (N - j)) * K A v j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range N, (1 + b) * (‖A‖ * ‖v j‖ ^ 2) := by
          refine sum_le_sum fun j hj => ?_
          rw [abs_mul]
          exact mul_le_mul (hw j hj) (abs_K_le A v j) (abs_nonneg _) (by linarith)
      _ = (1 + b) * (‖A‖ * ∑ j ∈ range N, ‖v j‖ ^ 2) := by rw [← mul_sum, ← mul_sum]
  rw [abs_mul, abs_of_pos h1b] at main
  rw [div_mul_eq_mul_div, le_div_iff₀ h1b, mul_comm]
  exact main

/-- Equality case. For a scale-invariant block the generator is the identity, the kinetic
term is `‖v j‖²`, and the drift of `‖θ‖²` is given exactly by the same weights, which tend to
the constant `(1+β)/(1-β)` of `drift_bound_const`. -/
theorem drift_scale_invariant (b : ℝ)
    (h : HeavyBall (ContinuousLinearMap.id ℝ E) (fun _ => b) η θ v g) (N : ℕ) :
    (1 - b) * (‖θ N‖ ^ 2 - ‖θ 0‖ ^ 2) =
      ∑ j ∈ range N, (1 + b - 2 * b ^ (N - j)) * ‖v j‖ ^ 2 := by
  have := drift_const b h N
  simpa [Q, K, real_inner_self_eq_norm_sq] using this

/-- The previous velocity, with `vprev 0 = 0`. -/
def vprev (v : ℕ → E) : ℕ → E
  | 0 => 0
  | k + 1 => v k

lemma eta_g (b : ℝ) (h : HeavyBall A (fun _ => b) η θ v g) (k : ℕ) :
    η • g k = b • vprev v k - v k := by
  cases k with
  | zero => simp [vprev, h.vel0]
  | succ k => simp [vprev, h.vel]

/-- Discrete energy dissipation: the descent inequality of an `ℓ`-smooth loss bounds the
total squared step length by the loss decrease. -/
theorem sum_sq_le_of_descent (b ℓ : ℝ) (L : E → ℝ) (hη : 0 < η) (hb0 : 0 ≤ b)
    (h : HeavyBall A (fun _ => b) η θ v g)
    (hdesc : ∀ k, L (θ (k + 1)) ≤ L (θ k) + ⟪g k, v k⟫ + ℓ / 2 * ‖v k‖ ^ 2) (N : ℕ) :
    ((1 - b) / η - ℓ / 2) * ∑ k ∈ range N, ‖v k‖ ^ 2 ≤ L (θ 0) - L (θ N) := by
  set c := (1 - b) / η - ℓ / 2
  let En : ℕ → ℝ := fun k => L (θ k) + b / (2 * η) * ‖vprev v k‖ ^ 2
  have step : ∀ k, En (k + 1) + c * ‖v k‖ ^ 2 ≤ En k := by
    intro k
    have hX : ⟪g k, v k⟫ = (b * ⟪vprev v k, v k⟫ - ‖v k‖ ^ 2) / η := by
      rw [eq_div_iff hη.ne', mul_comm, ← real_inner_smul_left, eta_g b h k, inner_sub_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hI : 2 * ⟪vprev v k, v k⟫ ≤ ‖vprev v k‖ ^ 2 + ‖v k‖ ^ 2 := by
      have := norm_sub_sq_real (vprev v k) (v k)
      nlinarith [sq_nonneg ‖vprev v k - v k‖]
    have key : ⟪g k, v k⟫ + b / (2 * η) * ‖v k‖ ^ 2 + c * ‖v k‖ ^ 2 + ℓ / 2 * ‖v k‖ ^ 2
        - b / (2 * η) * ‖vprev v k‖ ^ 2
        = b / (2 * η) * (2 * ⟪vprev v k, v k⟫ - ‖v k‖ ^ 2 - ‖vprev v k‖ ^ 2) := by
      rw [hX]; simp only [c]; field_simp; ring
    have hneg : b / (2 * η) * (2 * ⟪vprev v k, v k⟫ - ‖v k‖ ^ 2 - ‖vprev v k‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hd := hdesc k
    have hv1 : vprev v (k + 1) = v k := rfl
    simp only [En, hv1]
    linarith
  have tele : ∀ n, En n + c * ∑ k ∈ range n, ‖v k‖ ^ 2 ≤ En 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ]; linarith [step n]
  have hE0 : En 0 = L (θ 0) := by simp [En, vprev]
  have hEN : L (θ N) ≤ En N := by
    simp only [En]; have : 0 ≤ b / (2 * η) * ‖vprev v N‖ ^ 2 := by positivity
    linarith
  linarith [tele N]

/-- Main discrete theorem for constant momentum: the drift of the symmetry quantity is at
most `(1+β)/(1-β) ‖A‖ (L₀ - L_N) / c` with `c = (1-β)/η - ℓ/2`. -/
theorem drift_bound_energy (b ℓ : ℝ) (L : E → ℝ) (hη : 0 < η) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hc : 0 < (1 - b) / η - ℓ / 2)
    (h : HeavyBall A (fun _ => b) η θ v g)
    (hdesc : ∀ k, L (θ (k + 1)) ≤ L (θ k) + ⟪g k, v k⟫ + ℓ / 2 * ‖v k‖ ^ 2) (N : ℕ) :
    |Q A (θ N) - Q A (θ 0)| ≤
      (1 + b) / (1 - b) * (‖A‖ * ((L (θ 0) - L (θ N)) / ((1 - b) / η - ℓ / 2))) := by
  refine (drift_bound_const b hb0 hb1 h N).trans ?_
  have hs : ∑ k ∈ range N, ‖v k‖ ^ 2 ≤ (L (θ 0) - L (θ N)) / ((1 - b) / η - ℓ / 2) := by
    rw [le_div_iff₀ hc, mul_comm]; exact sum_sq_le_of_descent b ℓ L hη hb0 h hdesc N
  have h1b : 0 < 1 - b := by linarith
  gcongr

/-! ### Nesterov's momentum schedule -/

/-- Nesterov's schedule `β k = (k-1)/(k+2)`. -/
noncomputable def nest (k : ℕ) : ℝ := ((k : ℝ) - 1) / ((k : ℝ) + 2)

lemma P_nest (h : HeavyBall A nest η θ v g) (N : ℕ) :
    P A θ v N = ∑ j ∈ range N,
      ((j : ℝ) * (j + 1) * (j + 2) / ((N : ℝ) * (N + 1) * (N + 2))) * K A v j := by
  induction N with
  | zero => simp [P_zero h]
  | succ n ih =>
    rw [P_succ h, ih, sum_range_succ]
    have hb : nest (n + 1) = (n : ℝ) / (n + 3) := by
      simp only [nest]; push_cast; ring_nf
    rw [hb, mul_add, mul_sum]
    push_cast
    congr 1
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · refine sum_congr rfl fun j _ => ?_
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp; ring
    · field_simp; ring

/-- Exact drift identity under Nesterov's schedule. The weight on step `j` is
`(j+1) - j(j+1)(j+2)/(N(N+1))`, which tends to `j+1` as `N → ∞`. -/
theorem drift_nesterov_schedule (h : HeavyBall A nest η θ v g) (N : ℕ) :
    Q A (θ N) - Q A (θ 0) = ∑ j ∈ range N,
      (((j : ℝ) + 1) - (j : ℝ) * (j + 1) * (j + 2) / ((N : ℝ) * (N + 1))) * K A v j := by
  induction N with
  | zero => simp
  | succ n ih =>
    have step := Q_step h n
    have key : Q A (θ (n + 1)) - Q A (θ 0) =
        (Q A (θ n) - Q A (θ 0)) + (2 * P A θ v n + K A v n) := by linarith
    rw [key, ih, P_nest h, sum_range_succ, mul_sum]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by positivity
      have : ∀ j ∈ range n,
          (((j : ℝ) + 1) - j * (j + 1) * (j + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))) * K A v j
          = (((j : ℝ) + 1) - j * (j + 1) * (j + 2) / ((n : ℝ) * (n + 1))) * K A v j
            + 2 * ((j : ℝ) * (j + 1) * (j + 2) / ((n : ℝ) * (n + 1) * (n + 2)) * K A v j) := by
        intro j _; field_simp; ring
      rw [sum_congr rfl this, sum_add_distrib]
      have hlast : ((n : ℝ) + 1) - n * (n + 1) * (n + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) = 1 := by
        field_simp; ring
      rw [hlast]; ring

end ViscosityML
