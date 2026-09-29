-- Prove2me | Theorems.Thm_lean_workbook_plus_40203
-- name    : lean_workbook_plus_40203
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6befc72b-e038-4394-9970-25d9d16d13c9
-- statement:
--   $ \frac{S}{E+I}=25 \Rightarrow E+I=\frac{S}{25} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40203 (S E I : ℝ) : S / (E + I) = 25 → E + I = S / 25   :=  by sorry
