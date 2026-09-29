-- Prove2me | Theorems.Thm_lean_workbook_plus_18949
-- name    : lean_workbook_plus_18949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d2cdfd47-812f-4d90-bd5b-e828375b0e14
-- statement:
--   Given $a+b+c=a^3+b^3+c^3=1$ and $a, b, c$ are real numbers, prove that $(ab+bc+ca)^3=a^3b^3+b^3c^3+c^3a^3$ using the identity $(x+y+z)^3=x^3+y^3+z^3+3(x+y+z)(xy+yz+xz)-3xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18949 (a b c : ℝ) (h₁ : a + b + c = 1) (h₂ : a^3 + b^3 + c^3 = 1) : (a * b + b * c + c * a)^3 = a^3 * b^3 + b^3 * c^3 + c^3 * a^3   :=  by sorry
