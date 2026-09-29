-- Prove2me | Theorems.Thm_lean_workbook_plus_53976
-- name    : lean_workbook_plus_53976
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fbda8ec0-1e20-45ec-ae51-307656e55ed9
-- statement:
--   Show that the equation $x^{3} -3a^{2}x = 2a^{3} \cosh T$ is satisfied by $2a\cosh (\frac{1}{3}T)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53976 (a T : ℝ) : (2*a*cosh (T/3))^3 - 3*a^2 * (2*a*cosh (T/3)) = 2*a^3*cosh T   :=  by sorry
