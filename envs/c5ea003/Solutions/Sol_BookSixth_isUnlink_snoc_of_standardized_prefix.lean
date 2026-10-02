-- Prove2me | solution 1 for BookSixth.isUnlink_snoc_of_standardized_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T08:51:20.061474+00:00
-- url     : https://prove2.me/submissions/91342439-fad1-432a-b4e6-436d5dc4d377

import Mathlib
import Definitions.Def_BookSixth

noncomputable section

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (P : ℝ → Space3 ≃ₜ Space3) (G : ℝ → Space3 ≃ₜ Space3)
    (hP : Continuous (fun p : ℝ × Space3 => P p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (P p.1).symm p.2) ∧
      (∀ x, P 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hPold : ∀ i, (P 1) '' C i = standardCircle i.val)
    (hGnew : (G 1) '' (P 1) '' D = standardCircle n)
    (hGpres : ∀ (t : ℝ) (i : ℕ), (G t) '' standardCircle i = standardCircle i) :
    IsUnlink (Fin.snoc C D) := by
  let H : ℝ → Space3 ≃ₜ Space3 := fun t => (P t).trans (G t)
  have hH : Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) := by
    refine ⟨?_, ?_, ?_⟩
    · have hmap : Continuous (fun p : ℝ × Space3 => (p.1, (P p.1) p.2)) :=
        continuous_fst.prodMk hP.1
      simpa [H, Function.comp_def] using hG.1.comp hmap
    · have hmap : Continuous (fun p : ℝ × Space3 => (p.1, (G p.1).symm p.2)) :=
        continuous_fst.prodMk hG.2.1
      simpa [H, Function.comp_def] using hP.2.1.comp hmap
    · intro x
      simp [H, hP.2.2 x, hG.2.2 x]
  refine ⟨H, hH.1, hH.2.1, hH.2.2, ?_⟩
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hone : (H 1) '' D = standardCircle n := by
      calc
        (H 1) '' D = (fun x => G 1 (P 1 x)) '' D := by
          simp [H, Homeomorph.trans_apply]
        _ = (G 1) '' ((P 1) '' D) := by rw [Set.image_image]
        _ = standardCircle n := hGnew
    simpa [Fin.snoc] using hone
  · have hone : (H 1) '' C i = standardCircle i.val := by
      calc
        (H 1) '' C i = (fun x => G 1 (P 1 x)) '' C i := by
          simp [H, Homeomorph.trans_apply]
        _ = (G 1) '' ((P 1) '' C i) := by rw [Set.image_image]
        _ = (G 1) '' standardCircle i.val := by rw [hPold i]
        _ = standardCircle i.val := hGpres 1 i
    simpa [Fin.snoc] using hone
