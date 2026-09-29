-- Prove2me | solution 1 for lean_workbook_plus_72719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:05.876115+00:00
-- url     : https://prove2.me/submissions/d239a525-4720-4898-a793-cf83f1772bf7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (q : ℝ → ℝ) (h₁ : q = fun (x : ℝ) => 1 / 2 * x - 3) : q x = -4 ↔ x = -2 := by
  intros
  grind
