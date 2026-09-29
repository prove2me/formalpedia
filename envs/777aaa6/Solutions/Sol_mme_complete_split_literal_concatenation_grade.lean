-- Prove2me | solution 1 for mme_complete_split_literal_concatenation_grade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:23:21.958457+00:00
-- url     : https://prove2.me/submissions/f5e04f49-9cda-4a38-baa7-56552f580019

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

set_option autoImplicit false
set_option warningAsError true

theorem solution (ell : ℕ) (hell : 1 ≤ ell) (x y : CompleteWord ell) :
    (∀ i, ((completeWordSplitEquiv ell hell).symm (x, y)) i =
      Fin.addCases x y (Fin.cast (completeWord_length_double ell hell) i)) ∧
    (completeWordSplitEquiv ell hell
      ((completeWordSplitEquiv ell hell).symm (x, y)) = (x, y)) ∧
    (∑ i, (((completeWordSplitEquiv ell hell).symm (x, y)) i).val) =
      (∑ i, (x i).val) + ∑ i, (y i).val := by
  refine ⟨fun _ ↦ rfl, (completeWordSplitEquiv ell hell).apply_symm_apply _, ?_⟩
  calc
    _ = ∑ i : Fin (2 ^ (ell - 1) + 2 ^ (ell - 1)), (Fin.addCases x y i : Fin 3).val :=
      (finCongr (completeWord_length_double ell hell)).sum_comp
        (fun i ↦ (Fin.addCases x y i : Fin 3).val)
    _ = _ := by
      rw [Fin.sum_univ_add]
      simp
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.addNat (2 ^ (ell - 1)) = Fin.natAdd (2 ^ (ell - 1)) i := by
        apply Fin.ext
        simp
      rw [hi]
      exact congrArg (fun z : Fin 3 ↦ z.val)
        (Fin.addCases_right (m := 2 ^ (ell - 1)) (n := 2 ^ (ell - 1))
          (motive := fun _ ↦ Fin 3) (left := x) (right := y) i)
