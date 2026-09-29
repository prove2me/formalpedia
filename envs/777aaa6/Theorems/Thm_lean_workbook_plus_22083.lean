-- Prove2me | Theorems.Thm_lean_workbook_plus_22083
-- name    : lean_workbook_plus_22083
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5cb3ee23-2802-4d39-a077-622071bc9b4f
-- statement:
--   prove $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a} \ge a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22083 : ∀ a b c : ℝ, (a^2 / b + b^2 / c + c^2 / a) ≥ a + b + c   :=  by sorry
