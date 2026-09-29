-- Prove2me | Theorems.Thm_lean_workbook_plus_8405
-- name    : lean_workbook_plus_8405
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7b756eff-cd53-4ad0-bf8a-51dcd458e1cc
-- statement:
--   $ \frac{3\binom{5}{3}\binom{2}{1}\binom{4}{2}}{\binom{9}{3}\binom{6}{3}\binom{3}{3}}=\frac{3}{14} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8405 :
  (3 * choose 5 3 * choose 2 1 * choose 4 2) / (choose 9 3 * choose 6 3 * choose 3 3) = 3 / 14   :=  by sorry
