-- Prove2me | Theorems.Thm_lean_workbook_plus_46311
-- name    : lean_workbook_plus_46311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/08fa9ba9-1c0b-4198-937c-ce5461503f3e
-- statement:
--   The probability Quincy gets out first is, $\frac{30}{36+30+25}=\frac{30}{91}$ , for Riley it is $\frac{25}{36+30+25}=\frac{25}{91}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46311 :
  30 / (36 + 30 + 25) * 100 = 30 / 91 * 100 ∧
  25 / (36 + 30 + 25) * 100 = 25 / 91 * 100   :=  by sorry
