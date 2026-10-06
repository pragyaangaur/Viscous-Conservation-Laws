import Mathlib

/-!
# The matrix law for two-layer linear networks under heavy ball

For a two-layer linear network `x ↦ W₂ W₁ x` the loss depends on `W₂ W₁` only, so its
gradients satisfy `G₁ W₁ᵀ = W₂ᵀ G₂` (`orth_of_factor`). Under gradient flow the matrix
`C = W₁ W₁ᵀ - W₂ᵀ W₂` is conserved. Under heavy ball with steps `V₁, V₂`:

* `C_step` : `C (k+1) - C k = P k + (P k)ᵀ + K k` with `P = V₁ W₁ᵀ - W₂ᵀ V₂` and
  `K = V₁ V₁ᵀ - V₂ᵀ V₂`.
* `P_succ` : `P (k+1) = β (k+1) • (P k + K k)` for any momentum schedule.
* `drift_matrix_const` : `(1-β) • (C N - C 0) = ∑ j < N, (1+β-2β^(N-j)) • K j`.
* `quad_drift` : the same identity for the quadratic form `x ↦ xᵀ (C N - C 0) x`, where
  `xᵀ K j x = ‖V₁ᵀ x‖² - ‖V₂ x‖²`.
* `trace_drift_bound` : for every symmetric `X` with `|xᵀ X x| ≤ xᵀ x` (operator norm at
  most one), `|tr (X (C N - C 0))| ≤ (1+β)/(1-β) ∑ j < N, (‖V₁ j‖_F² + ‖V₂ j‖_F²)`.
  Taking the supremum over such `X` gives the nuclear norm bound of the paper.
-/

set_option linter.unusedSectionVars false

open Matrix Finset

namespace ViscosityML.LinearNet

variable {r p q : Type*} [Fintype r] [Fintype p] [Fintype q] [DecidableEq r]

/-- Gradients of a loss of the form `ℓ (W₂ W₁)` are `G₁ = W₂ᵀ R` and `G₂ = R W₁ᵀ`, and they
satisfy the orthogonality used below. -/
lemma orth_of_factor (W₁ : Matrix r p ℝ) (W₂ : Matrix q r ℝ) (R : Matrix q p ℝ) :
    (W₂ᵀ * R) * W₁ᵀ = W₂ᵀ * (R * W₁ᵀ) := Matrix.mul_assoc _ _ _

/-- Heavy ball on a two-layer linear network. -/
structure HB (β : ℕ → ℝ) (η : ℝ) (W₁ V₁ G₁ : ℕ → Matrix r p ℝ)
    (W₂ V₂ G₂ : ℕ → Matrix q r ℝ) : Prop where
  orth : ∀ k, G₁ k * (W₁ k)ᵀ = (W₂ k)ᵀ * G₂ k
  pos₁ : ∀ k, W₁ (k + 1) = W₁ k + V₁ k
  pos₂ : ∀ k, W₂ (k + 1) = W₂ k + V₂ k
  vel₁0 : V₁ 0 = -(η • G₁ 0)
  vel₂0 : V₂ 0 = -(η • G₂ 0)
  vel₁ : ∀ k, V₁ (k + 1) = β (k + 1) • V₁ k - η • G₁ (k + 1)
  vel₂ : ∀ k, V₂ (k + 1) = β (k + 1) • V₂ k - η • G₂ (k + 1)

variable {β : ℕ → ℝ} {η : ℝ} {W₁ V₁ G₁ : ℕ → Matrix r p ℝ} {W₂ V₂ G₂ : ℕ → Matrix q r ℝ}

/-- The conserved matrix `C = W₁ W₁ᵀ - W₂ᵀ W₂`. -/
def C (W₁ : ℕ → Matrix r p ℝ) (W₂ : ℕ → Matrix q r ℝ) (k : ℕ) : Matrix r r ℝ :=
  W₁ k * (W₁ k)ᵀ - (W₂ k)ᵀ * W₂ k

/-- Cross term `P = V₁ W₁ᵀ - W₂ᵀ V₂`. -/
def P (W₁ V₁ : ℕ → Matrix r p ℝ) (W₂ V₂ : ℕ → Matrix q r ℝ) (k : ℕ) : Matrix r r ℝ :=
  V₁ k * (W₁ k)ᵀ - (W₂ k)ᵀ * V₂ k

/-- Kinetic term `K = V₁ V₁ᵀ - V₂ᵀ V₂`. -/
def K (V₁ : ℕ → Matrix r p ℝ) (V₂ : ℕ → Matrix q r ℝ) (k : ℕ) : Matrix r r ℝ :=
  V₁ k * (V₁ k)ᵀ - (V₂ k)ᵀ * V₂ k

lemma K_transpose (k : ℕ) : (K V₁ V₂ k)ᵀ = K V₁ V₂ k := by
  simp [K, transpose_sub, transpose_mul]

lemma C_step (h : HB β η W₁ V₁ G₁ W₂ V₂ G₂) (k : ℕ) :
    C W₁ W₂ (k + 1) - C W₁ W₂ k = P W₁ V₁ W₂ V₂ k + (P W₁ V₁ W₂ V₂ k)ᵀ + K V₁ V₂ k := by
  simp only [C, P, K, h.pos₁, h.pos₂, transpose_add, transpose_sub, transpose_mul,
    transpose_transpose, Matrix.add_mul, Matrix.mul_add]
  abel

lemma P_zero (h : HB β η W₁ V₁ G₁ W₂ V₂ G₂) : P W₁ V₁ W₂ V₂ 0 = 0 := by
  rw [P, h.vel₁0, h.vel₂0, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    h.orth 0]
  abel

lemma P_succ (h : HB β η W₁ V₁ G₁ W₂ V₂ G₂) (k : ℕ) :
    P W₁ V₁ W₂ V₂ (k + 1) = β (k + 1) • (P W₁ V₁ W₂ V₂ k + K V₁ V₂ k) := by
  have e₁ : V₁ (k + 1) * (W₁ (k + 1))ᵀ =
      β (k + 1) • (V₁ k * (W₁ k)ᵀ + V₁ k * (V₁ k)ᵀ) - η • (G₁ (k + 1) * (W₁ (k + 1))ᵀ) := by
    rw [h.vel₁, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, h.pos₁ k, transpose_add, Matrix.mul_add]
  have e₂ : (W₂ (k + 1))ᵀ * V₂ (k + 1) =
      β (k + 1) • ((W₂ k)ᵀ * V₂ k + (V₂ k)ᵀ * V₂ k) - η • ((W₂ (k + 1))ᵀ * G₂ (k + 1)) := by
    rw [h.vel₂, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h.pos₂ k, transpose_add, Matrix.add_mul]
  simp only [P, K]
  rw [e₁, e₂, h.orth (k + 1)]
  simp only [smul_add, smul_sub]
  abel

/-- For constant momentum the cross term is a geometric sum of past kinetic terms. -/
lemma P_const (b : ℝ) (h : HB (fun _ => b) η W₁ V₁ G₁ W₂ V₂ G₂) (N : ℕ) :
    P W₁ V₁ W₂ V₂ N = ∑ j ∈ range N, b ^ (N - j) • K V₁ V₂ j := by
  induction N with
  | zero => simp [P_zero h]
  | succ n ih =>
    rw [P_succ h, ih, sum_range_succ, smul_add, smul_sum]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have : n + 1 - j = (n - j) + 1 := by have := mem_range.mp hj; omega
      rw [smul_smul, this, pow_succ, mul_comm]
    · simp

/-- Exact matrix drift identity for constant momentum. -/
theorem drift_matrix_const (b : ℝ) (h : HB (fun _ => b) η W₁ V₁ G₁ W₂ V₂ G₂) (N : ℕ) :
    (1 - b) • (C W₁ W₂ N - C W₁ W₂ 0) =
      ∑ j ∈ range N, (1 + b - 2 * b ^ (N - j)) • K V₁ V₂ j := by
  induction N with
  | zero => simp
  | succ n ih =>
    have step := C_step h n
    have key : C W₁ W₂ (n + 1) - C W₁ W₂ 0 =
        (C W₁ W₂ n - C W₁ W₂ 0) + (P W₁ V₁ W₂ V₂ n + (P W₁ V₁ W₂ V₂ n)ᵀ + K V₁ V₂ n) := by
      rw [← step]; abel
    have hPT : (P W₁ V₁ W₂ V₂ n)ᵀ = P W₁ V₁ W₂ V₂ n := by
      rw [P_const b h n, transpose_sum]
      simp only [transpose_smul, K_transpose]
    rw [key, smul_add, ih, hPT, P_const b h n, sum_range_succ, Nat.add_sub_cancel_left]
    have hsplit : ∀ j ∈ range n, (1 + b - 2 * b ^ (n + 1 - j)) • K V₁ V₂ j =
        (1 + b - 2 * b ^ (n - j)) • K V₁ V₂ j + (2 * (1 - b)) • (b ^ (n - j) • K V₁ V₂ j) := by
      intro j hj
      have : n + 1 - j = (n - j) + 1 := by have := mem_range.mp hj; omega
      rw [this, smul_smul, ← add_smul, pow_succ]; congr 1; ring
    rw [sum_congr rfl hsplit, sum_add_distrib, ← smul_sum,
      show (1 + b - 2 * b ^ 1) = (1 - b) by ring, mul_smul, two_smul]
    simp only [smul_add]
    abel

/-! ### Quadratic form and trace bounds -/

/-- Squared Frobenius norm. -/
def frob2 {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

lemma quad_gram {n : Type*} [Fintype n] (V : Matrix r n ℝ) (x : r → ℝ) :
    x ⬝ᵥ ((V * Vᵀ) *ᵥ x) = (Vᵀ *ᵥ x) ⬝ᵥ (Vᵀ *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← transpose_transpose V, vecMul_transpose,
    transpose_transpose]

lemma quad_gram' {n : Type*} [Fintype n] (V : Matrix n r ℝ) (x : r → ℝ) :
    x ⬝ᵥ ((Vᵀ * V) *ᵥ x) = (V *ᵥ x) ⬝ᵥ (V *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The quadratic form of the kinetic term: `xᵀ K x = ‖V₁ᵀ x‖² - ‖V₂ x‖²`. -/
lemma quad_K (k : ℕ) (x : r → ℝ) :
    x ⬝ᵥ (K V₁ V₂ k *ᵥ x) =
      (V₁ k)ᵀ *ᵥ x ⬝ᵥ ((V₁ k)ᵀ *ᵥ x) - V₂ k *ᵥ x ⬝ᵥ (V₂ k *ᵥ x) := by
  rw [K, sub_mulVec, dotProduct_sub, quad_gram, quad_gram']

/-- Exact identity for the quadratic form of the drift. -/
theorem quad_drift (b : ℝ) (h : HB (fun _ => b) η W₁ V₁ G₁ W₂ V₂ G₂) (N : ℕ) (x : r → ℝ) :
    (1 - b) * (x ⬝ᵥ ((C W₁ W₂ N - C W₁ W₂ 0) *ᵥ x)) =
      ∑ j ∈ range N, (1 + b - 2 * b ^ (N - j)) *
        ((V₁ j)ᵀ *ᵥ x ⬝ᵥ ((V₁ j)ᵀ *ᵥ x) - V₂ j *ᵥ x ⬝ᵥ (V₂ j *ᵥ x)) := by
  have := congrArg (fun M : Matrix r r ℝ => x ⬝ᵥ (M *ᵥ x)) (drift_matrix_const b h N)
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul, sum_mulVec, dotProduct_sum] at this
  rw [this]
  exact sum_congr rfl fun j _ => by rw [quad_K]

/-- `tr (X V Vᵀ)` is a sum of quadratic forms of the columns of `V`. -/
lemma trace_gram {n : Type*} [Fintype n] (X : Matrix r r ℝ) (V : Matrix r n ℝ) :
    trace (X * (V * Vᵀ)) = ∑ j, (fun i => V i j) ⬝ᵥ (X *ᵥ fun i => V i j) := by
  calc trace (X * (V * Vᵀ))
      = ∑ i, ∑ k, ∑ j, X i k * (V k j * V i j) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, X i k * (V k j * V i j) :=
        sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k, X i k * (V k j * V i j) := Finset.sum_comm
    _ = _ := by
        refine sum_congr rfl fun j _ => ?_
        simp only [dotProduct, mulVec, Finset.mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
        ring

lemma trace_gram' {n : Type*} [Fintype n] (X : Matrix r r ℝ) (V : Matrix n r ℝ) :
    trace (X * (Vᵀ * V)) = ∑ j, (fun i => V j i) ⬝ᵥ (X *ᵥ fun i => V j i) := by
  have := trace_gram X Vᵀ
  simpa [transpose_transpose] using this

lemma abs_trace_gram_le {n : Type*} [Fintype n] (X : Matrix r r ℝ)
    (hX : ∀ x : r → ℝ, |x ⬝ᵥ (X *ᵥ x)| ≤ x ⬝ᵥ x) (V : Matrix r n ℝ) :
    |trace (X * (V * Vᵀ))| ≤ frob2 V := by
  rw [trace_gram]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun j _ => hX _).trans (le_of_eq ?_)
  simp only [frob2, dotProduct]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

lemma abs_trace_gram_le' {n : Type*} [Fintype n] (X : Matrix r r ℝ)
    (hX : ∀ x : r → ℝ, |x ⬝ᵥ (X *ᵥ x)| ≤ x ⬝ᵥ x) (V : Matrix n r ℝ) :
    |trace (X * (Vᵀ * V))| ≤ frob2 V := by
  rw [trace_gram']
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun j _ => hX _).trans (le_of_eq ?_)
  simp only [frob2, dotProduct]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

/-- Trace-duality form of the nuclear norm bound: for every `X` of operator norm at most one,
`|tr (X (C N - C 0))| ≤ (1+β)/(1-β) ∑ (‖V₁ j‖_F² + ‖V₂ j‖_F²)`. -/
theorem trace_drift_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (h : HB (fun _ => b) η W₁ V₁ G₁ W₂ V₂ G₂) (N : ℕ) (X : Matrix r r ℝ)
    (hX : ∀ x : r → ℝ, |x ⬝ᵥ (X *ᵥ x)| ≤ x ⬝ᵥ x) :
    |trace (X * (C W₁ W₂ N - C W₁ W₂ 0))| ≤
      (1 + b) / (1 - b) * ∑ j ∈ range N, (frob2 (V₁ j) + frob2 (V₂ j)) := by
  have h1b : 0 < 1 - b := by linarith
  have hK : ∀ j, |trace (X * K V₁ V₂ j)| ≤ frob2 (V₁ j) + frob2 (V₂ j) := by
    intro j
    rw [K, Matrix.mul_sub, trace_sub]
    exact (abs_sub _ _).trans (add_le_add (abs_trace_gram_le X hX _) (abs_trace_gram_le' X hX _))
  have hw : ∀ j ∈ range N, |1 + b - 2 * b ^ (N - j)| ≤ 1 + b := by
    intro j _
    have h0 : 0 ≤ b ^ (N - j) := pow_nonneg hb0 _
    have h1 : b ^ (N - j) ≤ 1 := pow_le_one₀ hb0 hb1.le
    rw [abs_le]; constructor <;> linarith
  have main : |(1 - b) * trace (X * (C W₁ W₂ N - C W₁ W₂ 0))| ≤
      (1 + b) * ∑ j ∈ range N, (frob2 (V₁ j) + frob2 (V₂ j)) := by
    rw [← smul_eq_mul, ← trace_smul, ← Matrix.mul_smul, drift_matrix_const b h N, Matrix.mul_sum,
      trace_sum]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul (hw j hj) (hK j) (abs_nonneg _) (by linarith)
  rw [abs_mul, abs_of_pos h1b] at main
  rw [div_mul_eq_mul_div, le_div_iff₀ h1b, mul_comm]
  exact main

end ViscosityML.LinearNet
