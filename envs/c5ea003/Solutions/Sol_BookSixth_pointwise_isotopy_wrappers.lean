-- Prove2me | solution 1 for BookSixth.pointwise_isotopy_wrappers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T09:07:37.259798+00:00
-- url     : https://prove2.me/submissions/23771968-0edc-4dde-aa51-dccf2615b55d

import Mathlib
import Definitions.Def_BookSixth

noncomputable section

open scoped BigOperators
open BookSixth

/-- An isotopy built from a pointwise time map and a pointwise time inverse. -/
theorem wrappers_iso_basic_pw (A B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hA : Continuous (fun p : ℝ × (Fin 3 → ℝ) => A p.1 p.2))
    (hB : Continuous (fun p : ℝ × (Fin 3 → ℝ) => B p.1 p.2))
    (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
    (h0 : ∀ x, A 0 x = x) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ t x, H t x = A t x) := by
  refine ⟨fun t =>
    { toFun := A t, invFun := B t, left_inv := hBA t, right_inv := hAB t,
      continuous_toFun := hA.comp (continuous_const.prodMk continuous_id),
      continuous_invFun := hB.comp (continuous_const.prodMk continuous_id) },
    hA, hB, h0, fun _ _ => rfl⟩

/-- The composition of two pointwise isotopies is again a pointwise isotopy. -/
theorem wrappers_iso_comp_pw (F G : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hF : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ t x, H t x = F t x))
    (hG : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t x)) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t (F t x)) := by
  obtain ⟨H1, c1, d1, e1, f1⟩ := hF
  obtain ⟨H2, c2, d2, e2, f2⟩ := hG
  refine ⟨fun t => (H1 t).trans (H2 t), ?_, ?_, ?_, fun t x => ?_⟩
  · exact c2.comp (continuous_fst.prodMk c1)
  · exact d1.comp (continuous_fst.prodMk d2)
  · intro x; simp [e1, e2]
  · rw [Homeomorph.trans_apply, f1, f2]

/-- An angle that turns a real pair into a coordinate direction. -/
theorem wrappers_angle_pw (a b : ℝ) :
    ∃ θ : ℝ, Real.sin θ * a + Real.cos θ * b = 0 ∧ 0 ≤ Real.cos θ * a - Real.sin θ * b := by
  by_cases h : a = 0 ∧ b = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp [h.1, h.2]
  · have hz : (⟨a, b⟩ : ℂ) ≠ 0 := by
      intro hz
      apply h
      exact ⟨congrArg Complex.re hz, congrArg Complex.im hz⟩
    refine ⟨-Complex.arg ⟨a, b⟩, ?_, ?_⟩
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      ring
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      have : 0 ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ :=
        div_nonneg (by nlinarith [mul_self_nonneg a, mul_self_nonneg b]) (norm_nonneg _)
      calc (0 : ℝ) ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ := this
        _ = _ := by ring

/-- The three generic pieces, bundled into a single importable statement. -/
theorem solution :
    (∀ (A B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (hA : Continuous (fun p : ℝ × (Fin 3 → ℝ) => A p.1 p.2))
      (hB : Continuous (fun p : ℝ × (Fin 3 → ℝ) => B p.1 p.2))
      (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
      (h0 : ∀ x, A 0 x = x),
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = A t x)) ∧
    (∀ (F G : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (hF : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = F t x))
      (hG : ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t x)),
      ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
        Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
        (∀ x, H 0 x = x) ∧ (∀ t x, H t x = G t (F t x))) ∧
    (∀ a b : ℝ, ∃ θ : ℝ, Real.sin θ * a + Real.cos θ * b = 0 ∧
        0 ≤ Real.cos θ * a - Real.sin θ * b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hA hB hAB hBA h0
    exact wrappers_iso_basic_pw A B hA hB hAB hBA h0
  · intro F G hF hG
    exact wrappers_iso_comp_pw F G hF hG
  · intro a b
    exact wrappers_angle_pw a b

end
