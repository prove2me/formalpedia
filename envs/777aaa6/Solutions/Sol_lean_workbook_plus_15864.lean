-- Prove2me | solution 1 for lean_workbook_plus_15864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:37.226396+00:00
-- url     : https://prove2.me/submissions/3cccf924-a96d-49da-beb9-c34917c4ad36

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b : ℝ, 1 + |a| + |b| ≠ 0 ∧ 1 + |a| ≠ 0 ∧ 1 + |b| ≠ 0 →
  |a| / (1 + |a| + |b|) + |b| / (1 + |a| + |b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
  intro a b h
  clear h
  apply add_le_add
  · exact div_le_div_of_nonneg_left (abs_nonneg a) (by positivity) (by linarith [abs_nonneg b])
  · exact div_le_div_of_nonneg_left (abs_nonneg b) (by positivity) (by linarith [abs_nonneg a])
