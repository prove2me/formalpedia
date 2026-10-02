-- Prove2me | solution 1 for BookSixth.isUnlink_pair_second_moves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T09:20:21.34777+00:00
-- url     : https://prove2.me/submissions/07f0ae2e-a80d-4d66-b604-132d0f84222d

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_isUnlink_path_image

noncomputable section

open scoped BigOperators
open BookSixth

theorem solution (A B B' : Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hA : ∀ t, K t '' A = A)
    (hB : K 1 '' B = B')
    (hAB : IsUnlink (![A, B] : Fin 2 → Set Space3)) :
    IsUnlink (![A, B'] : Fin 2 → Set Space3) := by
  have h : IsUnlink (fun i : Fin 2 => K 1 '' ![A, B] i) := by
    refine BookSixth.isUnlink_path_image (C := ![A, B]) K
      ⟨hK.1, hK.2.1, hK.2.2⟩ hAB
  have hpair : (fun i : Fin 2 => K 1 '' ![A, B] i) = ![A, B'] := by
    funext i
    fin_cases i
    · exact hA 1
    · exact hB
  rw [hpair] at h
  exact h
