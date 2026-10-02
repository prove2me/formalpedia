-- Prove2me | solution 1 for BookSixth.isUnlink_pair_of_isUnlink_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:59:09.684321+00:00
-- url     : https://prove2.me/submissions/630dedd3-bdd1-4345-a427-7449e6917ca1

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standard_pair_relabel_lt
import Theorems.Thm_BookSixth_isUnlink_pair_swap

open scoped BigOperators
open BookSixth

theorem trans_continuous {A B : ℝ → Space3 ≃ₜ Space3}
    (hA : Continuous (fun p : ℝ × Space3 => (A p.1) p.2))
    (hB : Continuous (fun p : ℝ × Space3 => (B p.1) p.2))
    (hAi : Continuous (fun p : ℝ × Space3 => (A p.1).symm p.2))
    (hBi : Continuous (fun p : ℝ × Space3 => (B p.1).symm p.2)) :
    Continuous (fun p : ℝ × Space3 => (A p.1).trans (B p.1) p.2) := by
  have hmap : Continuous (fun p : ℝ × Space3 =>
      (p.1, (A p.1) p.2)) := continuous_fst.prodMk hA
  simpa [Homeomorph.trans_apply, Function.comp_def] using hB.comp hmap

theorem trans_inverse_continuous {A B : ℝ → Space3 ≃ₜ Space3}
    (hA : Continuous (fun p : ℝ × Space3 => (A p.1) p.2))
    (hB : Continuous (fun p : ℝ × Space3 => (B p.1) p.2))
    (hAi : Continuous (fun p : ℝ × Space3 => (A p.1).symm p.2))
    (hBi : Continuous (fun p : ℝ × Space3 => (B p.1).symm p.2)) :
    Continuous (fun p : ℝ × Space3 =>
      (A p.1).trans (B p.1) |>.symm p.2) := by
  have hmap : Continuous (fun p : ℝ × Space3 =>
      (p.1, (B p.1).symm p.2)) := continuous_fst.prodMk hBi
  simpa [Homeomorph.symm_trans_apply, Function.comp_def] using hAi.comp hmap

theorem solution {n : ℕ} (C : Fin n → Set Space3)
    (hC : IsUnlink C) (i j : Fin n) (hij : i ≠ j) :
    IsUnlink (![C i, C j] : Fin 2 → Set Space3) := by
  have forward : ∀ (i j : Fin n), i < j →
      IsUnlink (![C i, C j] : Fin 2 → Set Space3) := by
    intro i j hil
    obtain ⟨R, hR1, hR2, hR0, hRi, hRj⟩ :=
      BookSixth.standard_pair_relabel_lt
        (i := i.val) (j := j.val) (by exact_mod_cast hil)
    obtain ⟨H, hH1, hH2, hH0, hHend⟩ := hC
    let K : ℝ → Space3 ≃ₜ Space3 := fun t => (H t).trans (R t)
    have hK1 : Continuous (fun p : ℝ × Space3 => (K p.1) p.2) := by
      simpa [K] using trans_continuous hH1 hR1 hH2 hR2
    have hK2 : Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) := by
      simpa [K] using trans_inverse_continuous hH1 hR1 hH2 hR2
    refine ⟨K, hK1, hK2, ?_, ?_⟩
    · intro x
      change R 0 (H 0 x) = x
      calc
        R 0 (H 0 x) = H 0 x := hR0 _
        _ = x := hH0 x
    · intro k
      fin_cases k
      · change (K 1) '' C i = standardCircle 0
        calc
          (K 1) '' C i = (fun x => R 1 (H 1 x)) '' C i := by rfl
          _ = R 1 '' ((H 1) '' C i) := by rw [Set.image_image]
          _ = R 1 '' standardCircle i.val := by rw [hHend i]
          _ = standardCircle 0 := hRi
      · change (K 1) '' C j = standardCircle 1
        calc
          (K 1) '' C j = (fun x => R 1 (H 1 x)) '' C j := by rfl
          _ = R 1 '' ((H 1) '' C j) := by rw [Set.image_image]
          _ = R 1 '' standardCircle j.val := by rw [hHend j]
          _ = standardCircle 1 := hRj
  rcases lt_or_gt_of_ne hij with hil | hji
  · exact forward i j hil
  · exact BookSixth.isUnlink_pair_swap (forward j i hji)
