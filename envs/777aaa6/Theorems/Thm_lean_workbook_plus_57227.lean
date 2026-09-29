-- Prove2me | Theorems.Thm_lean_workbook_plus_57227
-- name    : lean_workbook_plus_57227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2457473b-0e40-4bfd-859f-5e2d299bb5fa
-- statement:
--   Prove that $\mathbb{Q}$ has the Archimedean property.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57227 : ∀ x y : ℚ, x > 0 → y > 0 → ∃ n : ℕ, y < n * x   :=  by sorry
