-- Prove2me | Theorems.Thm_lean_workbook_plus_12070
-- name    : lean_workbook_plus_12070
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/54078f10-902f-4edf-aa3f-1fe0cfb0892c
-- statement:
--   prove that: $(ab^2+bc^2+cd^2+a^2d)(a^2b+b^2c+c^2d+d^2a)\geq (acd+abd+abc+bcd)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12070 : ∀ a b c d : ℝ, (a * b ^ 2 + b * c ^ 2 + c * d ^ 2 + a ^ 2 * d) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * d + d ^ 2 * a) ≥ (a * c * d + a * b * d + b * c * a + b * d * c) ^ 2   :=  by sorry
