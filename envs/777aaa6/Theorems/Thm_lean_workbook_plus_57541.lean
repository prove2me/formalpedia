-- Prove2me | Theorems.Thm_lean_workbook_plus_57541
-- name    : lean_workbook_plus_57541
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9a32852c-79ce-45c6-b5dd-ec40713b5fb1
-- statement:
--   Let $a$ , $b$ , $c$ be real numbers. Prove that $a^3+b^3+c^3 \ge a^2b+b^2c+c^2a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57541 : ∀ a b c : ℝ, a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a   :=  by sorry
