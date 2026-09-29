-- Prove2me | Theorems.Thm_lean_workbook_plus_7745
-- name    : lean_workbook_plus_7745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fc98177f-8905-4b17-91bf-c328181b83f0
-- statement:
--   Given $a + b + c + d = 0$ , prove that $a^3 + b^3 + c^3 + d^3 = 3(abc + bcd + cda + dab).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7745 : ∀ a b c d : ℝ, a + b + c + d = 0 → a^3 + b^3 + c^3 + d^3 = 3 * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
