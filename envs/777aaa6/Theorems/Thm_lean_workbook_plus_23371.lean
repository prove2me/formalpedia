-- Prove2me | Theorems.Thm_lean_workbook_plus_23371
-- name    : lean_workbook_plus_23371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/28cc71a9-52db-4c16-99d1-5188a0f4fb78
-- statement:
--   Let $a,\,b,\,c$ are non-negative real numners. Prove that $a^4+b^4+c^4 \geqslant abc(a+b+c)+ \frac{14}{5} \cdot ab (a-b)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23371 : ∀ a b c : ℝ, a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) + (14 / 5) * a * b * (a - b)^2   :=  by sorry
