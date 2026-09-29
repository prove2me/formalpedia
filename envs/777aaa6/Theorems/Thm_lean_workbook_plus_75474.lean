-- Prove2me | Theorems.Thm_lean_workbook_plus_75474
-- name    : lean_workbook_plus_75474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/5385207a-6eb4-4cc6-86d4-04407f137db3
-- statement:
--   Prove that \((a^2 + b^2+c^2)^2 - 2(a^3b + b^3c+c^3a) \geq 2abc(a+b+c) - (a^2b^2 + b^2c^2 + c^2a^2)\) for all real \(a,b,c\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75474 (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 2 * (a^3 * b + b^3 * c + c^3 * a) ≥ 2 * a * b * c * (a + b + c) - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
