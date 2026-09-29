-- Prove2me | solution 1 for mme_dwz_nonholeFraction_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:08:07.047213+00:00
-- url     : https://prove2.me/submissions/f5372175-e656-4cf5-b9a8-dc885f05f991

import Mathlib.Tactic
import Definitions.Def_mme_dwz_hole_cover_data

open Finset
open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {Block : Type u} [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (copy : BrokenBlockCopy Block)
    (hseven : 7 * Fintype.card Block ≤ 8 * copy.nonholes.card) :
    (7 : ℝ) / 8 ≤ nonholeFraction copy := by
  rw [nonholeFraction]
  have hcardNat : 0 < Fintype.card Block := Fintype.card_pos
  have hcardReal : (0 : ℝ) < Fintype.card Block := by
    exact_mod_cast hcardNat
  have hsevenReal :
      (7 : ℝ) * Fintype.card Block ≤
        8 * (copy.nonholes.card : ℝ) := by
    exact_mod_cast hseven
  rw [le_div_iff₀ hcardReal]
  nlinarith
