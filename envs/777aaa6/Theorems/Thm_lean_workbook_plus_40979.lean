-- Prove2me | Theorems.Thm_lean_workbook_plus_40979
-- name    : lean_workbook_plus_40979
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9c5714f5-e5ee-4f16-a1bd-2e385de65610
-- statement:
--   Solution $\frac{3\cdot5\cdot4+3\cdot5\cdot\binom42}{3^5}=\frac{60+90}{243}=\boxed{\frac{50}{81}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40979 :
  (3 * 5 * 4 + 3 * 5 * ( choose 4 2)) / (3^5) = 50 / 81   :=  by sorry
