-- Prove2me | solution 1 for lean_workbook_plus_70637
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:29.34905+00:00
-- url     : https://prove2.me/submissions/25684b9b-da02-4094-b1ac-8afddec64aa9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution {z : ℤ} (h : z % 2 = 0) : z^2 ≡ 0 [ZMOD 4] := by
  have hz : z = 2 * (z / 2) := by omega
  change z^2 % 4 = 0 % 4
  conv_lhs => rw [hz]
  norm_num [mul_pow, Int.mul_emod]
