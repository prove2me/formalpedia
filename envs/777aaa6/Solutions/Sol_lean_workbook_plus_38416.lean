-- Prove2me | solution 1 for lean_workbook_plus_38416
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:10.402321+00:00
-- url     : https://prove2.me/submissions/00777762-74af-439b-9785-f79bb0bb87a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : |b - c| < a ∧ |c - a| < b ∧ |a - b| < c := by
  intros
  grind
