-- Prove2me | Theorems.Thm_lean_workbook_plus_2915
-- name    : lean_workbook_plus_2915
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a5af9071-6fe9-43f4-b03c-31aa25d9c351
-- statement:
--   Show that $\frac{1}{3n+1}+\frac{1}{3n+2}-\frac{1}{3n+3}= \frac{9n^2+18n+7}{(3n+3)(3n+2)(3n+1)}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2915 (n : ℕ) : (1 / (3 * n + 1) + 1 / (3 * n + 2) - 1 / (3 * n + 3) : ℚ) = (9 * n ^ 2 + 18 * n + 7) / ((3 * n + 3) * (3 * n + 2) * (3 * n + 1))   :=  by sorry
