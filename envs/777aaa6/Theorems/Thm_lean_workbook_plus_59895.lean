-- Prove2me | Theorems.Thm_lean_workbook_plus_59895
-- name    : lean_workbook_plus_59895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b8f62636-0558-4e65-ab83-e786f5c7c461
-- statement:
--   Let $a, b \ge 0.$ Prove that \n$$ \left ( a^2+b+\frac{3}{4} \right )\left ( b^2+a+\frac{3}{4} \right )\geq \left ( 2a+\frac{1}{2} \right )\left ( 2b+\frac{1}{2} \right ). $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59895 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^2 + b + 3/4) * (b^2 + a + 3/4) ≥ (2*a + 1/2) * (2*b + 1/2)   :=  by sorry
