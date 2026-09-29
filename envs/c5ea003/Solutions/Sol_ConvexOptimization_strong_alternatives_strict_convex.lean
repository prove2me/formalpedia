-- Prove2me | solution 1 for ConvexOptimization.strong_alternatives_strict_convex
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T14:51:27.092204+00:00
-- url     : https://prove2.me/submissions/14ae53d6-a51f-4f32-8c07-9bac4f81a851

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality
import Theorems.Thm_ConvexOptimization_slater_strong_duality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace StrongAltAux

/-- Lift a pair `(x, s)` to the extra-variable space `ℝⁿ⁺¹` used by B&V's
auxiliary problem (5.81). -/
noncomputable def lift {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) s)

/-- The `x`-part of a point of `ℝⁿ⁺¹`. -/
noncomputable def proj {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => y i.castSucc)

/-- The `s`-part of a point of `ℝⁿ⁺¹`. -/
def lastc {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := y (Fin.last n)

variable {n : ℕ}

@[simp] theorem lift_castSucc (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) (i : Fin n) :
    lift x s i.castSucc = x i := by simp [lift]

@[simp] theorem lift_last (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    lift x s (Fin.last n) = s := by simp [lift]

@[simp] theorem proj_apply (y : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    proj y i = y i.castSucc := by simp [proj]

@[simp] theorem proj_lift (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) : proj (lift x s) = x := by
  ext i; simp

@[simp] theorem lastc_lift (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) : lastc (lift x s) = s := by
  simp [lastc]

theorem proj_smul_add (c d : ℝ) (y z : EuclideanSpace ℝ (Fin (n + 1))) :
    proj (c • y + d • z) = c • proj y + d • proj z := by
  ext i; simp

theorem lastc_smul_add (c d : ℝ) (y z : EuclideanSpace ℝ (Fin (n + 1))) :
    lastc (c • y + d • z) = c * lastc y + d * lastc z := by simp [lastc]

theorem proj_zero : proj (0 : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by ext i; simp

theorem lift_sum {p : ℕ} (g : Fin p → ℝ) (v : Fin p → EuclideanSpace ℝ (Fin n)) :
    ∑ j, g j • lift (v j) 0 = lift (∑ j, g j • v j) 0 := by
  ext k
  induction k using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem inner_lift_zero (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin (n + 1))) : ⟪lift x 0, y⟫ = ⟪x, proj y⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc]

end StrongAltAux

open ConvexOptimization in
theorem solution {n mm p : ℕ}
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ) (hCQ : ∃ x, ∀ j, ⟪a j, x⟫ = b j) :
    (∃ x, (∀ i, fc i x < 0) ∧ ∀ j, ⟪a j, x⟫ = b j) ↔
      ¬∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
        0 ≤ dualFunction 0 fc a b lam nu := by
  constructor
  · -- Weak direction: a strictly feasible point kills every dual certificate.
    rintro ⟨x, hx, hxe⟩ ⟨lam, nu, hlam, hlamne, hge⟩
    obtain ⟨k, hk⟩ : ∃ k, lam k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hlamne (funext hcon)
    have hkpos : 0 < lam k := lt_of_le_of_ne (hlam k) (Ne.symm hk)
    have hval : dualFunction 0 fc a b lam nu
        ≤ ((lagrangian 0 fc a b x lam nu : ℝ) : EReal) := iInf_le _ x
    have hneg : lagrangian 0 fc a b x lam nu < 0 := by
      have h1 : ∑ i, lam i * fc i x < 0 := by
        have hterm : ∀ i ∈ Finset.univ, lam i * fc i x ≤ (0 : ℝ) := fun i _ =>
          mul_nonpos_of_nonneg_of_nonpos (hlam i) (hx i).le
        have hk' : lam k * fc k x < 0 := mul_neg_of_pos_of_neg hkpos (hx k)
        have := Finset.sum_lt_sum (f := fun i => lam i * fc i x) (g := fun _ => (0 : ℝ))
          hterm ⟨k, Finset.mem_univ k, hk'⟩
        simpa using this
      have h2 : ∑ j, nu j * (⟪a j, x⟫ - b j) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hxe j]; ring
      simp only [lagrangian, Pi.zero_apply, h2, add_zero, zero_add]
      exact h1
    have hfin : (0 : EReal) ≤ ((lagrangian 0 fc a b x lam nu : ℝ) : EReal) := le_trans hge hval
    rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff] at hfin
    linarith
  · -- Strong direction: B&V's auxiliary problem (5.81) plus Slater's theorem.
    intro hno
    by_contra hnox
    push_neg at hnox
    obtain ⟨x₀, hx₀⟩ := hCQ
    -- The auxiliary problem: minimize `s` subject to `fᵢ x - s ≤ 0`, `Ax = b`.
    set F₀ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y => StrongAltAux.lastc y with hF₀def
    set FC : Fin mm → EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
      fun i y => fc i (StrongAltAux.proj y) - StrongAltAux.lastc y with hFCdef
    set A : Fin p → EuclideanSpace ℝ (Fin (n + 1)) :=
      fun j => StrongAltAux.lift (a j) 0 with hAdef
    have hF₀c : ConvexOn ℝ Set.univ F₀ := by
      refine ⟨convex_univ, fun y _ z _ c d _ _ _ => ?_⟩
      simp only [hF₀def, StrongAltAux.lastc_smul_add, smul_eq_mul]
      exact le_refl _
    have hFCc : ∀ i, ConvexOn ℝ Set.univ (FC i) := by
      intro i
      refine ⟨convex_univ, fun y _ z _ c d hc hd hcd => ?_⟩
      have h1 := (hfc i).2 (Set.mem_univ (StrongAltAux.proj y))
        (Set.mem_univ (StrongAltAux.proj z)) hc hd hcd
      simp only [smul_eq_mul] at h1
      simp only [hFCdef, StrongAltAux.proj_smul_add, StrongAltAux.lastc_smul_add, smul_eq_mul]
      linarith
    have hAinner : ∀ (j : Fin p) (y : EuclideanSpace ℝ (Fin (n + 1))),
        ⟪A j, y⟫ = ⟪a j, StrongAltAux.proj y⟫ := fun j y => StrongAltAux.inner_lift_zero (a j) y
    have hAli : LinearIndependent ℝ A := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      rw [hAdef] at hg
      rw [StrongAltAux.lift_sum] at hg
      have : StrongAltAux.proj (StrongAltAux.lift (∑ j, g j • a j) 0) = StrongAltAux.proj 0 := by
        rw [hg]
      rw [StrongAltAux.proj_lift, StrongAltAux.proj_zero] at this
      exact Fintype.linearIndependent_iff.mp ha g this j
    -- A strictly feasible point for the auxiliary problem.
    set s₀ : ℝ := 1 + ∑ i, |fc i x₀| with hs₀def
    set ys : EuclideanSpace ℝ (Fin (n + 1)) := StrongAltAux.lift x₀ s₀ with hysdef
    have hys_ineq : ∀ i, FC i ys < 0 := by
      intro i
      have h1 : fc i x₀ ≤ |fc i x₀| := le_abs_self _
      have h2 : |fc i x₀| ≤ ∑ i, |fc i x₀| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (fc i x₀)) (Finset.mem_univ i)
      simp only [hFCdef, hysdef, StrongAltAux.proj_lift, StrongAltAux.lastc_lift, hs₀def]
      linarith
    have hys_eq : ∀ j, ⟪A j, ys⟫ = b j := by
      intro j
      rw [hAinner, hysdef, StrongAltAux.proj_lift]
      exact hx₀ j
    -- The optimal value of the auxiliary problem is `≥ 0`: a negative value would
    -- solve the strict system.
    have hlb : ∀ w ∈ F₀ '' feasibleSet FC A b, (0 : ℝ) ≤ w := by
      rintro _ ⟨y, hy, rfl⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨j, hj⟩ := hnox (StrongAltAux.proj y) (fun i => by
        have h1 := hy.1 i
        simp only [hFCdef] at h1
        simp only [hF₀def] at hcon
        linarith)
      exact hj (by have h2 := hy.2 j; rwa [hAinner] at h2)
    have hbdd : BddBelow (F₀ '' feasibleSet FC A b) := ⟨0, hlb⟩
    have hne : (F₀ '' feasibleSet FC A b).Nonempty :=
      ⟨F₀ ys, ⟨ys, ⟨fun i => (hys_ineq i).le, hys_eq⟩, rfl⟩⟩
    have hInf : (0 : ℝ) ≤ sInf (F₀ '' feasibleSet FC A b) := le_csInf hne hlb
    -- Slater's theorem for the auxiliary problem.
    obtain ⟨lam, nu, hlam, hdual⟩ :=
      ConvexOptimization.slater_strong_duality F₀ hF₀c FC hFCc A hAli b ys hys_ineq hys_eq hbdd
    -- Evaluate the Lagrangian of the auxiliary problem at lifted points.
    have hLeq : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        lagrangian F₀ FC A b (StrongAltAux.lift x s) lam nu
          = s + ∑ i, lam i * (fc i x - s) + ∑ j, nu j * (⟪a j, x⟫ - b j) := by
      intro x s
      have hAlift : ∀ (j : Fin p) (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ⟪A j, StrongAltAux.lift x s⟫ = ⟪a j, x⟫ := by
        intro j x s; rw [hAinner, StrongAltAux.proj_lift]
      simp only [lagrangian, hF₀def, hFCdef, StrongAltAux.proj_lift, StrongAltAux.lastc_lift,
        hAlift]
    have hkey : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        0 ≤ s + ∑ i, lam i * (fc i x - s) + ∑ j, nu j * (⟪a j, x⟫ - b j) := by
      intro x s
      have h1 : dualFunction F₀ FC A b lam nu
          ≤ ((lagrangian F₀ FC A b (StrongAltAux.lift x s) lam nu : ℝ) : EReal) :=
        iInf_le _ _
      rw [hdual, hLeq] at h1
      have := le_trans (by exact_mod_cast hInf :
        ((0 : ℝ) : EReal) ≤ ((sInf (F₀ '' feasibleSet FC A b) : ℝ) : EReal)) h1
      exact_mod_cast this
    -- Rewrite in the form `s (1 - 1ᵀλ) + (Σ λᵢ fᵢ x + Σ νⱼ (⟪aⱼ,x⟫ - bⱼ))`.
    have hexpand : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        s + ∑ i, lam i * (fc i x - s) + ∑ j, nu j * (⟪a j, x⟫ - b j)
          = s * (1 - ∑ i, lam i)
            + (∑ i, lam i * fc i x + ∑ j, nu j * (⟪a j, x⟫ - b j)) := by
      intro x s
      have h : ∑ i, lam i * (fc i x - s) = ∑ i, (lam i * fc i x - s * lam i) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    -- `1ᵀλ = 1`, otherwise the auxiliary dual function would be `-∞`.
    have hsum1 : ∑ i, lam i = 1 := by
      by_contra hcon
      set K : ℝ := ∑ i, lam i * fc i x₀ + ∑ j, nu j * (⟪a j, x₀⟫ - b j) with hKdef
      have hne' : (1 : ℝ) - ∑ i, lam i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hcon)
      have h := hkey x₀ (-(K + 1) / (1 - ∑ i, lam i))
      rw [hexpand] at h
      rw [div_mul_cancel₀ _ hne'] at h
      linarith
    have hlamne : lam ≠ 0 := by
      intro hcon
      rw [hcon] at hsum1
      simp at hsum1
    -- Conclude: `g(λ, ν) ≥ 0` for the original problem with zero objective.
    refine hno ⟨lam, nu, hlam, hlamne, ?_⟩
    refine le_iInf fun x => ?_
    have h := hkey x 0
    rw [hexpand, hsum1] at h
    simp only [sub_self, mul_zero, zero_add] at h
    have : (0 : ℝ) ≤ lagrangian 0 fc a b x lam nu := by
      simp only [lagrangian, Pi.zero_apply, zero_add]
      linarith
    exact_mod_cast this
