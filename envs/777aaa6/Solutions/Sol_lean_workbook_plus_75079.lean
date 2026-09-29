-- Prove2me | solution 1 for lean_workbook_plus_75079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:58.820611+00:00
-- url     : https://prove2.me/submissions/82e40865-eaf9-49ea-818b-c0de621da9d5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, (1 - a) * (1 - b) * (1 - c) ≥ 0 ↔ 1 + a * b + b * c + c * a ≥ a + b + c + a * b * c := by
  intro a b c
  intros
  grind
