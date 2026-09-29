-- Prove2me | Theorems.Thm_lean_workbook_plus_78403
-- name    : lean_workbook_plus_78403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/37e33a1a-65bb-413c-b12e-9a2cf7a1ea82
-- statement:
--   Let $a = (2 + \sqrt{5})^{2n}$ and $b = (2 - \sqrt{5})^{2n}$ . The above expression reduces to $\frac{a^3 + b^3}{a + b} = a^2 - ab + b^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78403 (a b : ℝ) (n : ℕ) : a = (2 + Real.sqrt 5)^(2 * n) ∧ b = (2 - Real.sqrt 5)^(2 * n) → (a^3 + b^3) / (a + b) = a^2 - a * b + b^2   :=  by sorry
