-- Prove2me | Theorems.Thm_lean_workbook_plus_60396
-- name    : lean_workbook_plus_60396
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ea97e780-5411-4f8a-9127-2d517290cbad
-- statement:
--   If $a, b, c\in\mathbb{R}$ , prove that \n $$(a^2+1)(b^2+1)(c^2+1)\ge 2|a+b+c|$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60396 : ∀ a b c : ℝ, (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 2 * |a + b + c|   :=  by sorry
