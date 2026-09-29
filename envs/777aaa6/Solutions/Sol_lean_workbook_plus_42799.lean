-- Prove2me | solution 1 for lean_workbook_plus_42799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:45.028456+00:00
-- url     : https://prove2.me/submissions/522f8bbb-2339-4606-9979-32c99825331e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f g : ℕ)
  (h₀ : 0 < f ∧ 0 < g)
  (h₁ : 6 * f + 9 * g = 36) :
  (f, g) = (3, 2) ∨ (f, g) = (6, 0) ∨ (f, g) = (0, 4) := by
  intros
  grind
