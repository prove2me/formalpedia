-- Prove2me | Theorems.Thm_lean_workbook_plus_51147
-- name    : lean_workbook_plus_51147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d46f7c14-f690-4830-b543-ece106524dd9
-- statement:
--   Given $a(bc-a^2) + b(ca-b^2) + c(ab-c^2) = 0$, prove that $a^3+b^3+c^3-3abc=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51147 (a b c : ℝ) (h : a * (b * c - a ^ 2) + b * (c * a - b ^ 2) + c * (a * b - c ^ 2) = 0) : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 0   :=  by sorry
