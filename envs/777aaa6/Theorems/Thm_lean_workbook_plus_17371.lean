-- Prove2me | Theorems.Thm_lean_workbook_plus_17371
-- name    : lean_workbook_plus_17371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/edf9f9df-647b-4f92-9e08-0839d8a26986
-- statement:
--   Prove that if $a > b$, then $a^3 + a^2b \ge b^3 + ab^2$. When does equality hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17371 (a b : ℝ) (h₁ : a > b) : a^3 + a^2 * b ≥ b^3 + a * b^2   :=  by sorry
