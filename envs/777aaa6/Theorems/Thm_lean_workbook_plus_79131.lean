-- Prove2me | Theorems.Thm_lean_workbook_plus_79131
-- name    : lean_workbook_plus_79131
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e0317d80-59b6-4ef7-880c-620b036a9715
-- statement:
--   Vasc had a stronger inequality: $ \frac{a^5}{a^4+b^4}+\frac{b^5}{b^4+c^4}+\frac{c^5}{c^4+a^4} \ge \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79131 : ∀ a b c : ℝ, (a ^ 5 / (a ^ 4 + b ^ 4) + b ^ 5 / (b ^ 4 + c ^ 4) + c ^ 5 / (c ^ 4 + a ^ 4)) ≥ 1 / 2   :=  by sorry
