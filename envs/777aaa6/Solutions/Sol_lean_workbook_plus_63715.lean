-- Prove2me | solution 1 for lean_workbook_plus_63715
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:17.448258+00:00
-- url     : https://prove2.me/submissions/ec396179-93e5-42c1-a9a5-85c0e366ce82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (A B : Finset ℕ) : A = {5, 6, 7, 8, 9, 10} ∧ B = {1, 2, 3, 4, 5, 6} → A ∪ B = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by
  intros
  grind
