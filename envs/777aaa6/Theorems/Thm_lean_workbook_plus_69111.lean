-- Prove2me | Theorems.Thm_lean_workbook_plus_69111
-- name    : lean_workbook_plus_69111
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0906cefa-51d6-49ea-9f21-611ba0eff0ab
-- statement:
--   I think this is better:\n $\frac{1}{a(b+c)}+\frac{1}{b(a+c)}+\frac{1}{c(a+b)}\leq\frac{18}{23}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69111 : ∀ a b c : ℝ, (1 / (a * (b + c)) + 1 / (b * (a + c)) + 1 / (c * (a + b))) ≤ (18:ℝ) / 23   :=  by sorry
