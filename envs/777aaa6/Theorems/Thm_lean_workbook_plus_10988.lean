-- Prove2me | Theorems.Thm_lean_workbook_plus_10988
-- name    : lean_workbook_plus_10988
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/34887443-2182-48fe-8ce2-5e4e6bbe73f1
-- statement:
--   The probability is $\frac{2}{6^5}$ for each favorable outcome. Permute this by multiplying by $5!$ to get $\frac{240}{6^5}=\boxed{\frac{5}{162}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10988 :
  ((2:ℝ) / (6^5)) * (5!) = (5:ℝ) / 162   :=  by sorry
