-- Prove2me | Theorems.Thm_lean_workbook_plus_79135
-- name    : lean_workbook_plus_79135
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e86f7a21-888a-4f98-b402-e53acef747bd
-- statement:
--   Prove that \n $ (a+b+c+d)^4+(a+b-c-d)^4+(a-b+c-d)^4+(a-b-c+d)^4-(a+b+c-d)^4-(a+b-c+d)^4-(a-b+c+d)^4-(-a+b+c+d)^4=192abcd$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79135 (a b c d : ℝ) : (a + b + c + d) ^ 4 + (a + b - c - d) ^ 4 + (a - b + c - d) ^ 4 + (a - b - c + d) ^ 4 - (a + b + c - d) ^ 4 - (a + b - c + d) ^ 4 - (a - b + c + d) ^ 4 - (-a + b + c + d) ^ 4 = 192 * a * b * c * d   :=  by sorry
