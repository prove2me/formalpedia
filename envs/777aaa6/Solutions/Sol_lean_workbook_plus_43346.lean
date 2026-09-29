-- Prove2me | solution 1 for lean_workbook_plus_43346
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:56.420711+00:00
-- url     : https://prove2.me/submissions/8986742c-8e78-4f19-994a-751b9bf97128

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k : ℂ)
  (h₀ : k ≠ 1)
  (h₁ : k ≠ -1) :
  1 / (k^2 - 1) = 1 / 2 * (1 / (k - 1) - 1 / (k + 1)) := by
  intros
  grind
