-- Prove2me | Theorems.Thm_lean_workbook_plus_37027
-- name    : lean_workbook_plus_37027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6a432059-8eba-405d-868d-b3fc29406b2e
-- statement:
--   To prove, $16(a^2+b^2+ab)(b^2+c^2+bc)\geq{9(a+b)^2(b+c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37027 (a b c : ℝ) : 16 * (a ^ 2 + b ^ 2 + a * b) * (b ^ 2 + c ^ 2 + b * c) ≥ 9 * (a + b) ^ 2 * (b + c) ^ 2   :=  by sorry
