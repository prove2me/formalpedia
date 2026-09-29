-- Prove2me | solution 1 for WallpaperRhythm.maximal_symmetry_has_two_patterns
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:52:20.802909+00:00
-- url     : https://prove2.me/submissions/d6538304-872a-41e4-9d7c-f4c497471110

import Mathlib
import Definitions.Def_Applications_WallpaperRhythm_QuotientEntropy

open WallpaperRhythm

theorem solution (α : Type*) [Fintype α] [Nonempty α] :
    Fintype.card (InvariantPattern α (maximalSymmetrySetoid α)) = 2 := by
  classical
  -- Under maximal symmetry every cell is identified, so the quotient is a singleton.
  have hquot : Fintype.card (Quotient (maximalSymmetrySetoid α)) = 1 := by
    refine Fintype.card_eq_one_iff.mpr ?_
    refine ⟨Quotient.mk (maximalSymmetrySetoid α) (Classical.arbitrary α), ?_⟩
    intro q
    induction q using Quotient.inductionOn with
    | _ a =>
      apply Quotient.sound
      trivial
  -- InvariantPattern ≃ (Quotient → Bool) and |Bool^1| = 2.
  have hequiv := InvariantPattern.quotientEquiv (maximalSymmetrySetoid α)
  have hcard := Fintype.card_congr hequiv
  -- |Quotient → Bool| = 2 ^ |Quotient| = 2^1 = 2
  have hfun : Fintype.card (Quotient (maximalSymmetrySetoid α) → Bool) = 2 := by
    rw [Fintype.card_fun, Fintype.card_bool, hquot]
    norm_num
  -- card InvariantPattern = card (Quotient → Bool)
  have : Fintype.card (InvariantPattern α (maximalSymmetrySetoid α)) =
      Fintype.card (Quotient (maximalSymmetrySetoid α) → Bool) := by
    exact (Fintype.card_congr hequiv).symm
  rw [this, hfun]
