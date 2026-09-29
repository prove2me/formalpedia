-- Prove2me | solution 1 for mme_complete_split_approx_consistent_two_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:38:08.843929+00:00
-- url     : https://prove2.me/submissions/4573dc3b-fdda-47c5-a3dc-8ef166b3774b

import Definitions.Def_mme_complete_split_concatenation
import Theorems.Thm_mme_complete_split_approx_consistent_coarsen

open MME MME.CompleteSplit MME.DWZComponentRestriction BigOperators
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution {ι : Type u} {ell N : ℕ} (hell : 1 ≤ ell)
    (label : ι → CompleteWord (ell + 1))
    (parent : Profile (ell + 1)) (left right : Profile ell)
    (hleft : ∀ x, ∑ y,
      parent.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        left.probability x)
    (hright : ∀ y, ∑ x,
      parent.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        right.probability y)
    (epsilon : ℝ≥0) (w : PowIndex ι N)
    (h : ApproxConsistent label parent epsilon w) :
    ApproxConsistent (fun a ↦ (completeWordSplitEquiv ell hell (label a)).1)
        left ((Fintype.card (CompleteWord (ell + 1)) : ℝ≥0) * epsilon) w ∧
      ApproxConsistent (fun a ↦ (completeWordSplitEquiv ell hell (label a)).2)
        right ((Fintype.card (CompleteWord (ell + 1)) : ℝ≥0) * epsilon) w := by
  classical
  let e := completeWordSplitEquiv ell hell
  have hleftPush (x : CompleteWord ell) :
      left.probability x = ∑ sigma : CompleteWord (ell + 1),
        if (e sigma).1 = x then parent.probability sigma else 0 := by
    calc
      left.probability x = ∑ y, parent.probability (e.symm (x, y)) := (hleft x).symm
      _ = ∑ xy : CompleteWord ell × CompleteWord ell,
          if xy.1 = x then parent.probability (e.symm xy) else 0 := by
        rw [Fintype.sum_prod_type]
        symm
        rw [Finset.sum_eq_single x]
        · simp
        · intro a _ ha
          simp [ha]
        · simp
      _ = _ := by
        simpa only [Equiv.apply_symm_apply] using
          e.symm.sum_comp
            (fun sigma ↦ if (e sigma).1 = x then parent.probability sigma else 0)
  have hrightPush (y : CompleteWord ell) :
      right.probability y = ∑ sigma : CompleteWord (ell + 1),
        if (e sigma).2 = y then parent.probability sigma else 0 := by
    calc
      right.probability y = ∑ x, parent.probability (e.symm (x, y)) := (hright y).symm
      _ = ∑ xy : CompleteWord ell × CompleteWord ell,
          if xy.2 = y then parent.probability (e.symm xy) else 0 := by
        rw [Fintype.sum_prod_type_right]
        symm
        rw [Finset.sum_eq_single y]
        · simp
        · intro a _ ha
          simp [ha]
        · simp
      _ = _ := by
        simpa only [Equiv.apply_symm_apply] using
          e.symm.sum_comp
            (fun sigma ↦ if (e sigma).2 = y then parent.probability sigma else 0)
  exact ⟨mme_complete_split_approx_consistent_coarsen
      label (fun sigma ↦ (e sigma).1) parent left hleftPush epsilon w h,
    mme_complete_split_approx_consistent_coarsen
      label (fun sigma ↦ (e sigma).2) parent right hrightPush epsilon w h⟩
