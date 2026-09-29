-- Prove2me | Theorems.Thm_lean_workbook_plus_33583
-- name    : lean_workbook_plus_33583
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3aa2f2fc-0ceb-4733-aae8-85353a15c886
-- statement:
--   Given $216=2^3 \times 3^3$, find integer solutions for $a, b, c$ such that $abc=216$ and $a + b + c =19$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33583 : ∃ a b c : ℤ, a * b * c = 216 ∧ a + b + c = 19   :=  by sorry
