-- Prove2me | Theorems.Thm_lean_workbook_plus_51667
-- name    : lean_workbook_plus_51667
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e2784554-a389-46ea-ad52-e9ef4bd54e6d
-- statement:
--   $\sum \frac{a}{b+c} \ge \sum \frac{2ab}{(c+b)(a+c)}$ $<=>a^3+b^3+c^3+3abc \ge \sum ab(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51667 : ∀ a b c : ℝ, a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a)   :=  by sorry
