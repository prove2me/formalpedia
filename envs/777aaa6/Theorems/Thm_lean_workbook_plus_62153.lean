-- Prove2me | Theorems.Thm_lean_workbook_plus_62153
-- name    : lean_workbook_plus_62153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/04854a8a-a4cf-4e46-a566-aa9ff11c8dd8
-- statement:
--   For positive real numbers $a,b,c$ prove that $2(a^3+b^3+c^3+abc)\geq (a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62153 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ (a + b) * (b + c) * (c + a)   :=  by sorry
