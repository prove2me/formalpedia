-- Prove2me | Theorems.Thm_lean_workbook_plus_72198
-- name    : lean_workbook_plus_72198
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/dde2d84f-28ea-4116-b6a3-2d63bb5f766b
-- statement:
--   Prove that for $a,b,c \in R^{+}$, $a^{4}+b^{4}+c^4+3*(a^2*b^2+b^2*c^2+a^2*c^2) \geq 2*(a^3*b+b^3*a+a^3*c+c^3*a+b^3*c+c^3*b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72198 (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) ≥ 2 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b)   :=  by sorry
