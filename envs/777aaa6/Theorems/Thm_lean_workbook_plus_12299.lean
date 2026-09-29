-- Prove2me | Theorems.Thm_lean_workbook_plus_12299
-- name    : lean_workbook_plus_12299
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8c34f29f-e894-4702-a8b0-ce89e761b887
-- statement:
--   with $t=\tan\left(\frac{x}{2}\right)$ we get \n $-{t}^{6}+4\,{t}^{5}-3\,{t}^{4}-16\,{t}^{3}-3\,{t}^{2}+12\,t-1=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12299 :
  ∀ x : ℝ,
    - (tan (x / 2))^6 + 4 * (tan (x / 2))^5 - 3 * (tan (x / 2))^4 - 16 * (tan (x / 2))^3 - 3 * (tan (x / 2))^2 + 12 * (tan (x / 2)) - 1 = 0   :=  by sorry
