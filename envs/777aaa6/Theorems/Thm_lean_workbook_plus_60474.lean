-- Prove2me | Theorems.Thm_lean_workbook_plus_60474
-- name    : lean_workbook_plus_60474
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/47227e98-9c98-479f-8419-e28f756a0a20
-- statement:
--   prove $ 4(ab + bc + ca)(a^2b + ab^2 + b^2c + bc^2 + c^2a + ca^2) \le (a + b + c)^2(a + b)(b + c)(c + a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60474 : ∀ a b c : ℝ, 4 * (a * b + b * c + c * a) * (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2) ≤ (a + b + c) ^ 2 * (a + b) * (b + c) * (c + a)   :=  by sorry
