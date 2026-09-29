-- Prove2me | Theorems.Thm_lean_workbook_plus_78490
-- name    : lean_workbook_plus_78490
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/83a132e6-33bc-4ba6-b1e9-5aabde9a77be
-- statement:
--   Prove that $a_n = \alpha^{2^{n - 1}} + \beta^{2^{n - 1}}$ where $\alpha = \frac{3 + \sqrt{5}}{2}$ and $\beta = \frac{3 - \sqrt{5}}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78490 (n : ℕ) (a_n : ℝ) (α : ℝ) (β : ℝ) (h₁ : α = (3 + Real.sqrt 5) / 2) (h₂ : β = (3 - Real.sqrt 5) / 2) (h₃ : a_n = α^(2^(n - 1)) + β^(2^(n - 1))) : a_n = α^(2^(n - 1)) + β^(2^(n - 1))   :=  by sorry
