-- Prove2me | solution 1 for lean_workbook_plus_69769
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:24:28.610396+00:00
-- url     : https://prove2.me/submissions/5816a0ba-d515-45c0-930a-c980e170a989

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution (a : ℤ) (h : 23 ∣ a^2+1) : 23 ∣ a^22+1 := by
  have hmod : a^2 ≡ (-1:ℤ) [ZMOD 23] := by
    apply Int.modEq_iff_dvd.mpr
    convert Int.dvd_neg.mpr h using 1 <;> ring
  have hsum := (hmod.pow 11).add_right 1
  apply Int.dvd_iff_emod_eq_zero.mpr
  change ((a^2)^11+1) % 23 = ((-1:ℤ)^11+1) % 23 at hsum
  norm_num [← pow_mul] at hsum
  exact hsum
