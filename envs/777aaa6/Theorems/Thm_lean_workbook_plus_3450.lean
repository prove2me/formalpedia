-- Prove2me | Theorems.Thm_lean_workbook_plus_3450
-- name    : lean_workbook_plus_3450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0d23d090-9d03-4d6a-814b-e9a3041031e5
-- statement:
--   Prove that is $a^2+b^2=1$ and $c^2+d^2=1$ then $|ac-bd|\leq1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3450 (a b c d : ℝ) (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) : |a * c - b * d| ≤ 1   :=  by sorry
