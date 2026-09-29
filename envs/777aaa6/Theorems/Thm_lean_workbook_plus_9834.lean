-- Prove2me | Theorems.Thm_lean_workbook_plus_9834
-- name    : lean_workbook_plus_9834
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bea23529-d6b6-4022-b6d8-d49990a3cf81
-- statement:
--   $\implies na-m=m-nb \iff n(a+b)=2m \iff \alpha =\dfrac{a+b}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9834 (a b m n : ℝ) : (n * a - m = m - n * b ↔ n * (a + b) = 2 * m)   :=  by sorry
