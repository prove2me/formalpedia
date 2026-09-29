-- Prove2me | Theorems.Thm_lean_workbook_plus_51323
-- name    : lean_workbook_plus_51323
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d7227bad-de96-4620-9044-106ecae7490e
-- statement:
--   (a) $\lim_{x \to 0} \frac{e^{-ax} - e^{-bx}}{x} = b-a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51323 (a b : ℝ) : ∀ a b : ℝ, a ≠ b → ∀ x : ℝ, x ≠ 0 → (Real.exp (-a * x) - Real.exp (-b * x)) / x = b - a   :=  by sorry
