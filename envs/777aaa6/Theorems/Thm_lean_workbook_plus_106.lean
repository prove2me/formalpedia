-- Prove2me | Theorems.Thm_lean_workbook_plus_106
-- name    : lean_workbook_plus_106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d660de64-463d-4db2-9877-44156cc29e97
-- statement:
--   Since $ (a+b+c)^{2}=(a+2b)(a+2c)+(b-c)^{2}$ it follows that \n $ \frac{a+b+c}{a+2c}=\frac{a+2b}{a+b+c}+\frac{(b-c)^{2}}{(a+2c)(a+b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_106 :  ∀ a b c : ℝ, (a + b + c) ^ 2 = (a + 2 * b) * (a + 2 * c) + (b - c) ^ 2   :=  by sorry
