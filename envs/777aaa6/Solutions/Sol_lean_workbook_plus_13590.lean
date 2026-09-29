-- Prove2me | solution 1 for lean_workbook_plus_13590
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:59.574134+00:00
-- url     : https://prove2.me/submissions/e8f51237-0d27-4b65-bde2-94c002fafbe9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y n : ℕ) :
  x^n * y^n * (x^2 + y^2) ≤ x^n * y^n * ((x + y)^2 - 2 * x * y) := by
  intros
  grind
