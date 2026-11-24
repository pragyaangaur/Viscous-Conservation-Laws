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

lemma Prob.L_sub_le (P : Prob F L A B γ G H) {x y : E} (hx : x ∈ B) (hy : y ∈ B) :
    L x - L y ≤ G * ‖x - y‖ := by
  have := P.conv.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := L)
    (f' := fun x => innerSL ℝ (F x)) (C := G)
    (fun x _ => (P.grad x).hasFDerivWithinAt)
    (fun x hx => by rw [innerSL_apply_norm]; exact P.bound x hx) hy hx
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

lemma Prob.contOn (P : Prob F L A B γ G H) : ContinuousOn F B := by
  have : LipschitzOnWith H.toNNReal F B := LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ P.Hpos.le]; exact P.lip x hx y hy)
  exact this.continuousOn

lemma Traj.contθ (T : Traj F B γ m θ v a) : ContinuousOn θ (Set.Ici 0) := fun t ht =>
  (T.dθ t ht).continuousAt.continuousWithinAt

lemma Traj.contv (T : Traj F B γ m θ v a) : ContinuousOn v (Set.Ici 0) := fun t ht =>
  (T.dv t ht).continuousAt.continuousWithinAt

lemma Traj.contFθ (P : Prob F L A B γ G H) (T : Traj F B γ m θ v a) :
    ContinuousOn (fun t => F (θ t)) (Set.Ici 0) :=
  P.contOn.comp T.contθ (fun t ht => T.mem t ht)

variable {φ φ' : ℝ → E}

lemma Flow.contφ (Fl : Flow F B γ φ φ') : ContinuousOn φ (Set.Ici 0) := fun t ht =>
  (Fl.dφ t ht).continuousAt.continuousWithinAt

lemma Flow.contFφ (P : Prob F L A B γ G H) (Fl : Flow F B γ φ φ') :
    ContinuousOn (fun t => F (φ t)) (Set.Ici 0) :=
  P.contOn.comp Fl.contφ (fun t ht => Fl.mem t ht)

/-- The derivative of the energy-type function `Ψ = (L θ - m/2 ‖v‖² - L φ) / γ`. -/
lemma Traj.hasDeriv_Psi (P : Prob F L A B γ G H) (T : Traj F B γ m θ v a)
    (Fl : Flow F B γ φ φ') {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (L (θ s) - m / 2 * ‖v s‖ ^ 2 - L (φ s)) / γ)
      (‖v t‖ ^ 2 + 2 * ⟪F (θ t), v t⟫ / γ + ‖F (φ t)‖ ^ 2 / γ ^ 2) t := by
  have hγ := P.gamma
  have hLθ : HasDerivAt (fun s => L (θ s)) ⟪F (θ t), v t⟫ t := by
    have := (P.grad (θ t)).comp_hasDerivAt t (T.dθ t ht)
    convert this using 1
    · rfl
    · simp
  have hLφ : HasDerivAt (fun s => L (φ s)) ⟪F (φ t), φ' t⟫ t := by
    have := (P.grad (φ t)).comp_hasDerivAt t (Fl.dφ t ht)
    convert this using 1
    · rfl
    · simp
  have hsq := (hasDerivAt_sq (T.dv t ht)).const_mul (m / 2)
  have hd := ((hLθ.sub hsq).sub hLφ).div_const γ
  refine hd.congr_deriv ?_
  have hmva : m * ⟪v t, a t⟫ = -⟪v t, F (θ t)⟫ - γ * ‖v t‖ ^ 2 := by
    have := congrArg (fun w => ⟪v t, w⟫) (T.ode t ht)
    simp only [inner_add_right, real_inner_smul_right, inner_neg_right,
      real_inner_self_eq_norm_sq] at this
    linarith
  have hφ : γ * ⟪F (φ t), φ' t⟫ = -‖F (φ t)‖ ^ 2 := by
    have := congrArg (fun w => ⟪F (φ t), w⟫) (Fl.ode t ht)
    simp only [real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq] at this
    linarith
  have hY : ⟪F (φ t), φ' t⟫ = -‖F (φ t)‖ ^ 2 / γ := by
    field_simp; linarith
  have e : m / 2 * (2 * ⟪v t, a t⟫) = m * ⟪v t, a t⟫ := by ring
  rw [e, hmva, hY, real_inner_comm (v t) (F (θ t))]
  field_simp
  ring

/-- The `L²` estimate on `[0, S]`: the velocity of the heavy ball is within `O(m)` of the
velocity `-F(φ)/γ` of gradient flow in the mean square. -/
theorem Traj.l2_le (P : Prob F L A B γ G H) (T : Traj F B γ m θ v a)
    (Fl : Flow F B γ φ φ') (hm : 0 < m) (h0 : θ 0 = φ 0) {S : ℝ} (hS : 0 ≤ S) :
    ∫ t in (0 : ℝ)..S, ‖v t + (1 / γ) • F (φ t)‖ ^ 2 ≤
      m * (G / γ ^ 2 * Real.exp (H * S / γ)) * (G / γ + 2 * G * H * S / γ ^ 2) := by
  have hγ := P.gamma
  have hH := P.Hpos
  have hG := P.Gnn
  set c := G / γ ^ 2 * Real.exp (H * S / γ) with hc
  have hc0 : 0 ≤ c := by positivity
  have he : ∀ t, 0 ≤ t → t ≤ S → ‖θ t - φ t‖ ≤ m * c := by
    intro t ht htS
    refine (T.dist_flow_le P Fl hm h0 ht).trans ?_
    rw [hc, ← mul_assoc, ← mul_div_assoc]
    have : Real.exp (H * t / γ) ≤ Real.exp (H * S / γ) := Real.exp_le_exp.2 (by gcongr)
    have h4 : 0 ≤ m * G / γ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h4
  let g : ℝ → ℝ := fun t => ‖v t‖ ^ 2 + 2 * ⟪F (θ t), v t⟫ / γ + ‖F (φ t)‖ ^ 2 / γ ^ 2
  have hsub : Set.Icc (0 : ℝ) S ⊆ Set.Ici 0 := Set.Icc_subset_Ici_self
  have hcv := T.contv.mono hsub
  have hcFθ := (T.contFθ P).mono hsub
  have hcFφ := (Fl.contFφ P).mono hsub
  have hg_cont : ContinuousOn g (Set.Icc 0 S) :=
    (((hcv.norm.pow 2).add (((hcFθ.inner hcv).const_mul 2).div_const γ)).add
      ((hcFφ.norm.pow 2).div_const _))
  have hw_cont : ContinuousOn (fun t => ‖v t + (1 / γ) • F (φ t)‖ ^ 2) (Set.Icc 0 S) :=
    ((hcv.add (continuousOn_const.smul hcFφ)).norm).pow 2
  have hI : Set.uIcc (0 : ℝ) S = Set.Icc 0 S := Set.uIcc_of_le hS
  have hPsi : ∫ t in (0 : ℝ)..S, g t =
      (L (θ S) - m / 2 * ‖v S‖ ^ 2 - L (φ S)) / γ -
        (L (θ 0) - m / 2 * ‖v 0‖ ^ 2 - L (φ 0)) / γ :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht => by rw [hI] at ht; exact T.hasDeriv_Psi P Fl ht.1)
      (by rw [hI] at *; exact hg_cont.intervalIntegrable_of_Icc hS)
  have hPsi0 : (L (θ 0) - m / 2 * ‖v 0‖ ^ 2 - L (φ 0)) / γ = 0 := by
    simp [h0, T.rest]
  have hPsiS : (L (θ S) - m / 2 * ‖v S‖ ^ 2 - L (φ S)) / γ ≤ G * (m * c) / γ := by
    rw [div_le_div_iff_of_pos_right hγ]
    have h1 := P.L_sub_le (T.mem S hS) (Fl.mem S hS)
    have h2 := he S hS le_rfl
    have h3 : 0 ≤ m / 2 * ‖v S‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hG]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) S,
      ‖v t + (1 / γ) • F (φ t)‖ ^ 2 ≤ g t + 2 * G * H * (m * c) / γ ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hvb := T.vel_bound P hm ht0
    have hdiff : ‖F (φ t) - F (θ t)‖ ≤ H * (m * c) := by
      have := P.lip _ (Fl.mem t ht0) _ (T.mem t ht0)
      rw [norm_sub_rev (φ t) (θ t)] at this
      exact this.trans (by gcongr; exact he t ht0 ht.2)
    have hexp : ‖v t + (1 / γ) • F (φ t)‖ ^ 2 =
        ‖v t‖ ^ 2 + 2 * ⟪v t, F (φ t)⟫ / γ + ‖F (φ t)‖ ^ 2 / γ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow]
      simp only [norm_div, norm_one, Real.norm_of_nonneg hγ.le]
      field_simp
    have hcs : ⟪v t, F (φ t) - F (θ t)⟫ ≤ G / γ * (H * (m * c)) := by
      refine (real_inner_le_norm _ _).trans ?_
      exact mul_le_mul hvb hdiff (norm_nonneg _) (by positivity)
    have : ⟪v t, F (φ t) - F (θ t)⟫ = ⟪v t, F (φ t)⟫ - ⟪F (θ t), v t⟫ := by
      rw [inner_sub_right, real_inner_comm (v t) (F (θ t))]
    rw [hexp]
    simp only [g]
    have e2 : 2 * G * H * (m * c) / γ ^ 2 = 2 * (G / γ * (H * (m * c))) / γ := by
      field_simp
    rw [e2]
    have : 2 * ⟪v t, F (φ t)⟫ / γ ≤ 2 * ⟪F (θ t), v t⟫ / γ + 2 * (G / γ * (H * (m * c))) / γ := by
      rw [← add_div, div_le_div_iff_of_pos_right hγ]
      linarith
    linarith
  calc ∫ t in (0 : ℝ)..S, ‖v t + (1 / γ) • F (φ t)‖ ^ 2
      ≤ ∫ t in (0 : ℝ)..S, (g t + 2 * G * H * (m * c) / γ ^ 2) :=
        integral_mono_on hS (by rw [← hI] at hw_cont; exact hw_cont.intervalIntegrable)
          (by
            rw [← hI] at hg_cont
            exact (hg_cont.add continuousOn_const).intervalIntegrable)
          hpt
    _ = (∫ t in (0 : ℝ)..S, g t) + S * (2 * G * H * (m * c) / γ ^ 2) := by
        rw [intervalIntegral.integral_add
          (by rw [← hI] at hg_cont; exact hg_cont.intervalIntegrable)
          intervalIntegrable_const]
        simp
        ring
    _ ≤ G * (m * c) / γ + S * (2 * G * H * (m * c) / γ ^ 2) := by
        rw [hPsi, hPsi0]; linarith
    _ = m * c * (G / γ + 2 * G * H * S / γ ^ 2) := by ring

end Setup

end ViscosityML
