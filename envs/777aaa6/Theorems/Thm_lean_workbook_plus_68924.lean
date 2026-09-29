-- Prove2me | Theorems.Thm_lean_workbook_plus_68924
-- name    : lean_workbook_plus_68924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0a5a108c-dc4a-45d6-9a7b-06402013b989
-- statement:
--   Prove that for real numbers $a, b, c$: $\left(\dfrac{a+b+c}{3}\right)^2\leq\dfrac{a^2+b^2+c^2}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68924 (a b c : ℝ) :
  ((a + b + c) / 3)^2 ≤ (a^2 + b^2 + c^2) / 3   :=  by sorry
