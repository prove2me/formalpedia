-- Prove2me | Theorems.Thm_lean_workbook_plus_27624
-- name    : lean_workbook_plus_27624
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/533ec740-f80c-4d30-938c-7f9fd8382698
-- statement:
--   Evaluate the product: $(log_{2}{3})(log_{3}{4})(log_{4}{5})(log_{5}{6})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27624 : (Real.logb 2 3) * (Real.logb 3 4) * (Real.logb 4 5) * (Real.logb 5 6) = Real.logb 2 6   :=  by sorry
