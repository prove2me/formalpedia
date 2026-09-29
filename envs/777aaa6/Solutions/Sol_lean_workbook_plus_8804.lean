-- Prove2me | solution 1 for lean_workbook_plus_8804
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:09.71014+00:00
-- url     : https://prove2.me/submissions/4a340dfa-a683-4c7f-a5ae-d71a3cb50469

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (n : ℕ) : 4 * (n + 1) ^ 3 > (2 * n + 1) ^ 2 * (n + 2) := by
  have he : 4 * (n + 1) ^ 3 = (2 * n + 1) ^ 2 * (n + 2) + 3 * n + 2 := by ring
  omega
