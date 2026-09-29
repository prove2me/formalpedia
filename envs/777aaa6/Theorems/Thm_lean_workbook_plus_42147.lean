-- Prove2me | Theorems.Thm_lean_workbook_plus_42147
-- name    : lean_workbook_plus_42147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a0204883-cc43-4fdc-8618-1d32f03cd34e
-- statement:
--   It suffices to show $\dbinom{j}{3} + j^2 =\dbinom{j+2}{3}$ for all positive integral $j$ . Simplifying gives $\dbinom{j}{3} + j^2 = \frac{1}{6} \cdot (j-2)(j-1)j+j^2=\frac{j}{6}((j-1)(j-2) + 6j) = j(j^2+3j+2) = \frac{j(j+1)(j+2)}{6} = \dbinom{j+2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42147 (j : ℕ) : (j + 2).choose 3 = j.choose 3 + j^2   :=  by sorry
