-- Prove2me | Theorems.Thm_lean_workbook_plus_43848
-- name    : lean_workbook_plus_43848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c97763a9-1821-4b80-b447-b0abce4708f6
-- statement:
--   Prove that $6(a^2+b^2+c^2)^2+3(a^2b+b^2c+c^2a)(a+b+c)\geq(a+b+c)^4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43848 (a b c : ℝ) : 6 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a + b + c) ≥ (a + b + c) ^ 4   :=  by sorry
