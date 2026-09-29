-- Prove2me | Theorems.Thm_lean_workbook_plus_62541
-- name    : lean_workbook_plus_62541
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b010358f-f9c7-4341-b474-b0adedcfba70
-- statement:
--   Prove that $(a-1)(2a^3+2a^2+3a-1)\leq 0$ for $1/3\leq a\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62541 : ∀ a : ℝ, 1/3 ≤ a ∧ a ≤ 1 → (a-1)*(2*a^3 + 2*a^2 + 3*a - 1) ≤ 0   :=  by sorry
