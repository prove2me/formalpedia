-- Prove2me | Theorems.Thm_lean_workbook_plus_30307
-- name    : lean_workbook_plus_30307
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7e0bdca4-e88d-4ba4-bc7f-37daf1f47c1c
-- statement:
--   Let $a,b$ be positive real numbers. Prove that $ab(a^2+b^2-2)\geq (a+b)(ab-1).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30307 : ∀ a b : ℝ, a > 0 ∧ b > 0 → a * b * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1)   :=  by sorry
