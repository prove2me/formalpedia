-- Prove2me | Theorems.Thm_lean_workbook_plus_10787
-- name    : lean_workbook_plus_10787
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d71fc942-58d2-4399-b608-5edc3248e39f
-- statement:
--   Given the system of equations: \n$ \begin{cases}g(x)=h(x)+k(x) \\\ g(-x)=h(x)-k(x) \end{cases}$ \nShow that $ h(x)=\frac{g(x)+g(-x)}{2}$ and $ k(x)=\frac{g(x)-g(-x)}{2}$ satisfy the conditions and prove their uniqueness.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10787 (g h k : ℝ → ℝ) : (∀ x, g x = h x + k x ∧ g (-x) = h x - k x) ↔ ∀ x, h x = (g x + g (-x)) / 2 ∧ k x = (g x - g (-x)) / 2   :=  by sorry
