-- Prove2me | solution 1 for BookSixth.isUnlink_pair_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T07:54:35.858972+00:00
-- url     : https://prove2.me/submissions/b2800362-d45f-4e90-89f6-e56996a1fdb3

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

namespace PairSwap

theorem iso_basic (A B : ℝ → Space3 → Space3)
    (hA : Continuous (fun p : ℝ × Space3 => A p.1 p.2))
    (hB : Continuous (fun p : ℝ × Space3 => B p.1 p.2))
    (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
    (h0 : ∀ x, A 0 x = x) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = A 1 x) := by
  refine ⟨fun t =>
    { toFun := A t, invFun := B t, left_inv := hBA t, right_inv := hAB t,
      continuous_toFun := hA.comp (continuous_const.prodMk continuous_id),
      continuous_invFun := hB.comp (continuous_const.prodMk continuous_id) },
    hA, hB, h0, fun x => rfl⟩

theorem Q_family :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = ![3 - x 0, -x 1, x 2]) := by
  obtain ⟨H, h1, h2, h0, h4⟩ := iso_basic
    (fun t x =>
      ![3 / 2 + Real.cos (t * Real.pi) * (x 0 - 3 / 2) -
          Real.sin (t * Real.pi) * x 1,
        Real.sin (t * Real.pi) * (x 0 - 3 / 2) +
          Real.cos (t * Real.pi) * x 1,
        x 2])
    (fun t x =>
      ![3 / 2 + Real.cos (t * Real.pi) * (x 0 - 3 / 2) +
          Real.sin (t * Real.pi) * x 1,
        -(Real.sin (t * Real.pi) * (x 0 - 3 / 2)) +
          Real.cos (t * Real.pi) * x 1,
        x 2])
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination (x 0 - 3 / 2) *
          Real.cos_sq_add_sin_sq (t * Real.pi)
      · linear_combination x 1 *
          Real.cos_sq_add_sin_sq (t * Real.pi))
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination (x 0 - 3 / 2) *
          Real.cos_sq_add_sin_sq (t * Real.pi)
      · linear_combination x 1 *
          Real.cos_sq_add_sin_sq (t * Real.pi))
    (by
      intro x
      funext i
      fin_cases i <;> simp)
  refine ⟨H, h1, h2, h0, ?_⟩
  intro x
  rw [h4]
  funext i
  fin_cases i <;>
    simp <;> ring

theorem map_standardCircle0 :
    (fun x => ![3 - x 0, -x 1, x 2]) '' standardCircle 0 = standardCircle 1 := by
  unfold standardCircle
  rw [← Set.range_comp]
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;>
      simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;>
      simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring

theorem map_standardCircle1 :
    (fun x => ![3 - x 0, -x 1, x 2]) '' standardCircle 1 = standardCircle 0 := by
  unfold standardCircle
  rw [← Set.range_comp]
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;>
      simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;>
      simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring

theorem isUnlink_swap {A B : Set Space3}
    (h : IsUnlink (![A, B] : Fin 2 → Set Space3)) :
    IsUnlink (![B, A] : Fin 2 → Set Space3) := by
  obtain ⟨H, hH1, hH2, hH0, hAB⟩ := h
  obtain ⟨Q, hQ1, hQ2, hQ0, hQone⟩ := Q_family
  have hHA : H 1 '' A = standardCircle 0 := by
    simpa using hAB 0
  have hHB : H 1 '' B = standardCircle 1 := by
    simpa using hAB 1
  let K : ℝ → Space3 ≃ₜ Space3 := fun t => (H t).trans (Q t)
  have hKf : Continuous (fun p : ℝ × Space3 => K p.1 p.2) := by
    simpa [K, Homeomorph.trans_apply] using
      hQ1.comp₂ continuous_fst hH1
  have hKi : Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) := by
    simpa [K, Homeomorph.symm_trans_apply] using
      hH2.comp₂ continuous_fst hQ2
  refine ⟨K, hKf, hKi, ?_, ?_⟩
  · intro x
    simp [K, Homeomorph.trans_apply, hH0, hQ0]
  · intro i
    fin_cases i
    · change (K 1) '' B = standardCircle 0
      calc
        (K 1) '' B = (fun x => Q 1 (H 1 x)) '' B := by
          apply Set.image_congr
          intro x hx
          rfl
        _ = Q 1 '' (H 1 '' B) := by
          simpa only [Function.comp_apply] using
            (Set.image_image (Q 1) (H 1) B).symm
        _ = Q 1 '' standardCircle 1 := by rw [hHB]
        _ = standardCircle 0 := by
          calc
            Q 1 '' standardCircle 1 =
                (fun x => ![3 - x 0, -x 1, x 2]) '' standardCircle 1 := by
                  apply Set.image_congr
                  intro x hx
                  exact hQone x
            _ = standardCircle 0 := map_standardCircle1
    · change (K 1) '' A = standardCircle 1
      calc
        (K 1) '' A = (fun x => Q 1 (H 1 x)) '' A := by
          apply Set.image_congr
          intro x hx
          rfl
        _ = Q 1 '' (H 1 '' A) := by
          simpa only [Function.comp_apply] using
            (Set.image_image (Q 1) (H 1) A).symm
        _ = Q 1 '' standardCircle 0 := by rw [hHA]
        _ = standardCircle 1 := by
          calc
            Q 1 '' standardCircle 0 =
                (fun x => ![3 - x 0, -x 1, x 2]) '' standardCircle 0 := by
                  apply Set.image_congr
                  intro x hx
                  exact hQone x
            _ = standardCircle 1 := map_standardCircle0

end PairSwap

theorem solution {A B : Set Space3}
    (h : IsUnlink (![A, B] : Fin 2 → Set Space3)) :
    IsUnlink (![B, A] : Fin 2 → Set Space3) :=
  PairSwap.isUnlink_swap h
