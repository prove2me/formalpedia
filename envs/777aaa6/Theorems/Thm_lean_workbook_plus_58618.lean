-- Prove2me | Theorems.Thm_lean_workbook_plus_58618
-- name    : lean_workbook_plus_58618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/677b4c0b-13aa-42ae-8d22-c180c00f7044
-- statement:
--   If $a,b,c\geq 0$ then prove that \n $a^{3}+b^{3}+c^{3}-3abc\geq 2 (\frac{b+c}{2}-a)^{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58618 (a b c : ℝ) (h : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) : a^3 + b^3 + c^3 - 3*a*b*c ≥ 2 * ((b + c) / 2 - a)^3   :=  by sorry
