-- Prove2me | Theorems.Thm_lean_workbook_plus_53732
-- name    : lean_workbook_plus_53732
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/42d89594-d2d0-4b33-9f99-38835c17fccf
-- statement:
--   Prove that $\frac{a^2}{a^2+b+c}+\frac{b^2 }{b^2+c+a}+\frac{c^2}{c^2+a+b}\leq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53732 : ∀ a b c : ℝ, (a^2 / (a^2 + b + c) + b^2 / (b^2 + c + a) + c^2 / (c^2 + a + b) : ℝ) ≤ 3 / 2   :=  by sorry
