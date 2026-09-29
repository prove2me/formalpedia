-- Prove2me | Theorems.Thm_lean_workbook_plus_72963
-- name    : lean_workbook_plus_72963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c8c51c30-d505-49ed-965e-515390c244d1
-- statement:
--   If a, b, c are real number then: $ 2(a+b+c)^4+3(a^2b^2+b^2c^2+c^2a^2)\ge 6(a+b+c)(a+b)(b+c)(c+a) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72963 (a b c : ℝ) : 2 * (a + b + c) ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 6 * (a + b + c) * (a + b) * (b + c) * (c + a)   :=  by sorry
