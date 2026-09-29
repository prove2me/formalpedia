-- Prove2me | Theorems.Thm_lean_workbook_plus_10623
-- name    : lean_workbook_plus_10623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/095cd649-e179-406c-a135-d8033fff7162
-- statement:
--   basically we want x>point of equality, since after the point of equality, the difference between 2x and sqrtx grow exponentially (2x is always bigger after point of equality). the 2 points of equality of $ \sqrt{x}=2x$ are $ \frac{1}{4}$ and 0. so we take x>the larger of the 2, or $ x>\frac{1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10623 : ∀ x > 1/4, Real.sqrt x < 2 * x   :=  by sorry
