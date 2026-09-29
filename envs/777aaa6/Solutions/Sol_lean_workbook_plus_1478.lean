-- Prove2me | solution 1 for lean_workbook_plus_1478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:55.817085+00:00
-- url     : https://prove2.me/submissions/e2dde094-2ac7-4489-b858-0e0056dd371e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a = 2) (hb : b = 2) (hc : c = 2) : (a - 1) ^ 2 / (a ^ 2 + 2) + (b - 1) ^ 2 / (b ^ 2 + 2) + (c - 1) ^ 2 / (c ^ 2 + 2) = 1 / 2 := by
  intros
  grind
