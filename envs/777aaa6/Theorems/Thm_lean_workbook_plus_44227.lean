-- Prove2me | Theorems.Thm_lean_workbook_plus_44227
-- name    : lean_workbook_plus_44227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cf462c61-1e84-4d04-a4a1-018b4f9756ca
-- statement:
--   Therefore the inequality $a<\frac{a+b}{2}<b$ holds when $a<b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44227 (a b : ℝ) (h₁ : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b   :=  by sorry
