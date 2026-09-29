-- Prove2me | Theorems.Thm_lean_workbook_plus_29215
-- name    : lean_workbook_plus_29215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/99dc0a03-5a66-476e-90d6-cf25ec6e4e89
-- statement:
--   Derive the inequality $a^2 + b^2 \geq 2ab$ from the trivial inequality $a^2 \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29215 : ∀ a b : ℝ, a^2 ≥ 0 → a^2 + b^2 ≥ 2 * a * b   :=  by sorry
