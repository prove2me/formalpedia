-- Prove2me | Theorems.Thm_lean_workbook_plus_1986
-- name    : lean_workbook_plus_1986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b7d82b5a-7f55-4ea7-9518-4d7975ca8735
-- statement:
--   answer is $x\in(-\infty, -5]\cup[3, \infty)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1986 (x : ℝ) : (x ≤ -5 ∨ 3 ≤ x) ↔ x ∈ Set.Iic (-5) ∪ Set.Ici 3   :=  by sorry
