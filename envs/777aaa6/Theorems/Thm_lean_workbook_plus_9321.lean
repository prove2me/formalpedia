-- Prove2me | Theorems.Thm_lean_workbook_plus_9321
-- name    : lean_workbook_plus_9321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3cab160d-aeab-412e-b19c-3c419ae35055
-- statement:
--   It was explained in a better post; here it is: $ x(y - x) \le \left(\frac{x + (y - x)}{2}\right)^2 = \frac{y^2}{4} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9321 (x y : ℝ) : x * (y - x) ≤ (x + (y - x))^2 / 4   :=  by sorry
