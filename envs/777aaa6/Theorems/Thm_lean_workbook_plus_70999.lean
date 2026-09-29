-- Prove2me | Theorems.Thm_lean_workbook_plus_70999
-- name    : lean_workbook_plus_70999
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5897cb17-42e0-45cd-ac65-06150912910e
-- statement:
--   The total number of ways given that you draw 20 red balls is $\frac{1}{2}{36 \choose 20}{59 \choose 30} + \frac{1}{2}{47 \choose 20}{54 \choose 30}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70999 :
  (choose 36 20 * choose 59 30 + choose 47 20 * choose 54 30) / 2 = choose 95 50   :=  by sorry
