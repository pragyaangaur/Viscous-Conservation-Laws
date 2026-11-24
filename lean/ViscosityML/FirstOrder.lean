import Mathlib
import ViscosityML.Limits

/-!
# First order in the mass (Theorem 3 of the paper)

Heavy ball `m θ'' + γ θ' = -F(θ)` with `F = ∇L` started at rest at `θ₀`, and gradient flow
`γ φ' = -F(φ)` from `θ₀`.
-/

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace
open intervalIntegral Filter Topology MeasureTheory

namespace ViscosityML

section Setup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Standing hypotheses on the loss, its gradient `F`, the generator `A` and the set `B`
that contains the trajectories. This is (H1) of the paper, without the compactness of `B`. -/
structure Prob (F : E → E) (L : E → ℝ) (A : E →L[ℝ] E) (B : Set E) (γ G H : ℝ) : Prop where
  symm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫
  orth : ∀ x, ⟪F x, A x⟫ = 0
  grad : ∀ x, HasFDerivAt L (innerSL ℝ (F x)) x
  gamma : 0 < γ
  Hpos : 0 < H
  Gnn : 0 ≤ G
  bound : ∀ x ∈ B, ‖F x‖ ≤ G
  lip : ∀ x ∈ B, ∀ y ∈ B, ‖F x - F y‖ ≤ H * ‖x - y‖
  conv : Convex ℝ B

/-- A heavy ball trajectory with mass `m`, started at rest, inside `B`. -/
structure Traj (F : E → E) (B : Set E) (γ m : ℝ) (θ v a : ℝ → E) : Prop where
  dθ : ∀ t, 0 ≤ t → HasDerivAt θ (v t) t
  dv : ∀ t, 0 ≤ t → HasDerivAt v (a t) t
  ode : ∀ t, 0 ≤ t → m • a t + γ • v t = -F (θ t)
  rest : v 0 = 0
  mem : ∀ t, 0 ≤ t → θ t ∈ B

/-- A gradient flow `γ φ' = -F(φ)` inside `B`. -/
structure Flow (F : E → E) (B : Set E) (γ : ℝ) (φ φ' : ℝ → E) : Prop where
  dφ : ∀ t, 0 ≤ t → HasDerivAt φ (φ' t) t
  ode : ∀ t, 0 ≤ t → γ • φ' t = -F (φ t)
  mem : ∀ t, 0 ≤ t → φ t ∈ B

variable {F : E → E} {L : E → ℝ} {A : E →L[ℝ] E} {B : Set E} {γ G H m : ℝ}
variable {θ v a : ℝ → E}

/-- The velocity of a heavy ball trajectory started at rest is at most `G / γ`. -/
theorem Traj.vel_bound (P : Prob F L A B γ G H) (T : Traj F B γ m θ v a) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) : ‖v t‖ ≤ G / γ := by
  have hγ := P.gamma
  set c := γ / m with hc
  have hc0 : 0 < c := div_pos hγ hm
  let f : ℝ → E := fun s => Real.exp (c * s) • v s
  have hexp : ∀ s, HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * s)) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul c).exp
    simpa [mul_comm] using this
  have hf : ∀ s, 0 ≤ s → HasDerivAt f (Real.exp (c * s) • a s + (c * Real.exp (c * s)) • v s) s :=
    fun s hs => (hexp s).smul (T.dv s hs)
  have hfc : ContinuousOn f (Set.Icc 0 t) := fun s hs =>
    (hf s hs.1).continuousAt.continuousWithinAt
  let Bf : ℝ → ℝ := fun s => G / γ * (Real.exp (c * s) - 1)
  have hBf : ∀ s, HasDerivAt Bf (G / m * Real.exp (c * s)) s := by
    intro s
    have := ((hexp s).sub_const 1).const_mul (G / γ)
    refine this.congr_deriv ?_
    simp only [hc]; field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hfc
    (f' := fun s => Real.exp (c * s) • a s + (c * Real.exp (c * s)) • v s)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) (B := Bf) (B' := fun s => G / m * Real.exp (c * s))
    (by simp [f, Bf, T.rest]) hBf (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have h1 : a s + c • v s = (1 / m) • (-F (θ s)) := by
        have h := T.ode s hs0
        calc a s + c • v s = (1 / m) • (m • a s + γ • v s) := by
              simp only [smul_add, smul_smul, hc]
              congr 1
              · rw [show (1 / m * m) = 1 by field_simp, one_smul]
              · congr 1; field_simp
          _ = _ := by rw [h]
      have e1 : Real.exp (c * s) • a s + (c * Real.exp (c * s)) • v s =
          Real.exp (c * s) • (a s + c • v s) := by
        simp only [smul_add, smul_smul, mul_comm]
      rw [e1, h1, norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / m)]
      have hFb := P.bound _ (T.mem s hs0)
      calc Real.exp (c * s) * (1 / m * ‖F (θ s)‖) ≤ Real.exp (c * s) * (1 / m * G) := by gcongr
        _ = G / m * Real.exp (c * s) := by ring) (x := t) ⟨ht, le_rfl⟩
  have hfn : ‖f t‖ = Real.exp (c * t) * ‖v t‖ := by
    simp only [f, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hfn] at key
  have hpos := Real.exp_pos (c * t)
  have : ‖v t‖ ≤ G / γ * (1 - Real.exp (-(c * t))) := by
    have e2 : Real.exp (-(c * t)) * Real.exp (c * t) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : ‖v t‖ = Real.exp (-(c * t)) * (Real.exp (c * t) * ‖v t‖) := by
      rw [← mul_assoc, e2, one_mul]
    rw [h3]
    calc Real.exp (-(c * t)) * (Real.exp (c * t) * ‖v t‖)
        ≤ Real.exp (-(c * t)) * (G / γ * (Real.exp (c * t) - 1)) := by
          gcongr
      _ = G / γ * (1 - Real.exp (-(c * t))) := by
          have : Real.exp (-(c * t)) * (G / γ * (Real.exp (c * t) - 1)) =
              G / γ * (Real.exp (-(c * t)) * Real.exp (c * t) - Real.exp (-(c * t))) := by ring
          rw [this, e2]
  refine this.trans ?_
  have : 0 ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
  have hG : 0 ≤ G / γ := div_nonneg P.Gnn hγ.le
  nlinarith

variable {φ φ' : ℝ → E}

/-- Grönwall estimate: the heavy ball trajectory stays within `(m G / γ²) exp(H t / γ)` of
the gradient flow with the same starting point. -/
theorem Traj.dist_flow_le (P : Prob F L A B γ G H) (T : Traj F B γ m θ v a)
    (Fl : Flow F B γ φ φ') (hm : 0 < m) (h0 : θ 0 = φ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖θ t - φ t‖ ≤ m * G / γ ^ 2 * Real.exp (H * t / γ) := by
  have hγ := P.gamma
  have hH := P.Hpos
  let f : ℝ → E := fun s => γ • (θ s - φ s) + m • v s
  let f' : ℝ → E := fun s => F (φ s) - F (θ s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f (f' s) s := by
    intro s hs
    have h1 := ((T.dθ s hs).sub (Fl.dφ s hs)).const_smul γ
    have h2 := (T.dv s hs).const_smul m
    refine (h1.add h2).congr_deriv ?_
    have e1 := T.ode s hs
    have e2 := Fl.ode s hs
    simp only [f']
    rw [smul_sub]
    have : γ • v s - γ • φ' s + m • a s = F (φ s) - F (θ s) := by
      rw [e2]
      have : m • a s = -F (θ s) - γ • v s := by rw [← e1]; abel
      rw [this]; abel
    exact this
  have hK : H / γ ≠ 0 := by positivity
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f') (a := 0) (b := t)
    (δ := 0) (K := H / γ) (ε := H * m * G / γ ^ 2)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt)
    (by simp [f, h0, T.rest])
    (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hlip := P.lip _ (Fl.mem s hs0) _ (T.mem s hs0)
      have hv := T.vel_bound P hm hs0
      have hθφ : γ • (θ s - φ s) = f s - m • v s := by simp [f]
      have hnorm : γ * ‖θ s - φ s‖ ≤ ‖f s‖ + m * (G / γ) := by
        have : ‖γ • (θ s - φ s)‖ = γ * ‖θ s - φ s‖ := by
          rw [norm_smul, Real.norm_of_nonneg hγ.le]
        rw [← this, hθφ]
        calc ‖f s - m • v s‖ ≤ ‖f s‖ + ‖m • v s‖ := norm_sub_le _ _
          _ ≤ ‖f s‖ + m * (G / γ) := by
            gcongr
            rw [norm_smul, Real.norm_of_nonneg hm.le]
            gcongr
      simp only [f']
      rw [norm_sub_rev] at hlip
      calc ‖F (φ s) - F (θ s)‖ ≤ H * ‖φ s - θ s‖ := by
            rw [← norm_neg (F (φ s) - F (θ s)), neg_sub]
            have := P.lip _ (T.mem s hs0) _ (Fl.mem s hs0)
            rw [norm_sub_rev (φ s) (θ s)]
            exact this
        _ = H * ‖θ s - φ s‖ := by rw [norm_sub_rev]
        _ ≤ H / γ * ‖f s‖ + H * m * G / γ ^ 2 := by
            have : ‖θ s - φ s‖ ≤ (‖f s‖ + m * (G / γ)) / γ := by
              rw [le_div_iff₀ hγ]; linarith
            calc H * ‖θ s - φ s‖ ≤ H * ((‖f s‖ + m * (G / γ)) / γ) := by gcongr
              _ = H / γ * ‖f s‖ + H * m * G / γ ^ 2 := by field_simp)
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK] at key
  have hv := T.vel_bound P hm ht
  have hnorm : γ * ‖θ t - φ t‖ ≤ ‖f t‖ + m * (G / γ) := by
    have : ‖γ • (θ t - φ t)‖ = γ * ‖θ t - φ t‖ := by
      rw [norm_smul, Real.norm_of_nonneg hγ.le]
    have hθφ : γ • (θ t - φ t) = f t - m • v t := by simp [f]
    rw [← this, hθφ]
    calc ‖f t - m • v t‖ ≤ ‖f t‖ + ‖m • v t‖ := norm_sub_le _ _
      _ ≤ ‖f t‖ + m * (G / γ) := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg hm.le]
        gcongr
  simp only [zero_mul, zero_add, sub_zero] at key
  have hex : H / γ * t = H * t / γ := by ring
  rw [hex] at key
  have e : H * m * G / γ ^ 2 / (H / γ) = m * G / γ := by field_simp
  rw [e] at key
  rw [show m * G / γ ^ 2 * Real.exp (H * t / γ) = (m * G / γ * (Real.exp (H * t / γ) - 1) + m * (G / γ)) / γ by
    field_simp; ring, le_div_iff₀ hγ]
  nlinarith [hnorm, key]

end Setup

end ViscosityML
