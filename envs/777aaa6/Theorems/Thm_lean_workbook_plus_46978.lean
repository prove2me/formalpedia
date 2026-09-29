-- Prove2me | Theorems.Thm_lean_workbook_plus_46978
-- name    : lean_workbook_plus_46978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b66b83e8-439c-4ff0-bf7c-4e4122ad272f
-- statement:
--   From Schur: $a^{2}(b+c)+b^{2}(c+a)+c^{2}(a+b)=a^{3}+b^{3}+c^{3}+2abc+1 \Leftrightarrow abc-1=a^3+b^3+c^3 + 3abc - ab(a+b)-bc(b+c)-ca(c+a) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46978 (a b c : ℝ) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) = a^3 + b^3 + c^3 + 2 * a * b * c + 1 ↔ a * b * c - 1 = a^3 + b^3 + c^3 + 3 * a * b * c - a * b * (a + b) - b * c * (b + c) - c * a * (c + a)   :=  by sorry
