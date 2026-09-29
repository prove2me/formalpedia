-- Prove2me | Theorems.Thm_lean_workbook_plus_18118
-- name    : lean_workbook_plus_18118
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b1b6c6b6-7a9b-426d-b343-d912cbc6215f
-- statement:
--   Find the inverse of $ f(x) = x^3 + x + 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18118 (f : ℝ → ℝ) (hf : f = fun x => x^3 + x + 1) : ∃ g, g = f⁻¹   :=  by sorry
