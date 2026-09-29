-- Prove2me | Theorems.Thm_lean_workbook_plus_9589
-- name    : lean_workbook_plus_9589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/23d013b6-26b4-458c-9507-76adca35ddb3
-- statement:
--   Prove that $ \boxed {\ \{x,y\}\subset [0,1]\ \implies\ (1 + xy)^2\ \ge\ \left(1 - x + x^2\right)\left(1 - y + y^2\right)\ }$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9589 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
  (1 + x * y) ^ 2 ≥ (1 - x + x ^ 2) * (1 - y + y ^ 2)   :=  by sorry
