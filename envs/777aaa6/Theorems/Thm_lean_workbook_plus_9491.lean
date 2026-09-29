-- Prove2me | Theorems.Thm_lean_workbook_plus_9491
-- name    : lean_workbook_plus_9491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/935f14e8-99a2-4a91-a91f-84ac9a59dac5
-- statement:
--   If a, b, c are real number then: $ (a^2+b^2+c^2)^2-2abc(a+b+c)\ge 2(a+b+c)(a-b)(b-c)(a-c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9491 (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 2 * a * b * c * (a + b + c) ≥ 2 * (a + b + c) * (a - b) * (b - c) * (a - c)   :=  by sorry
