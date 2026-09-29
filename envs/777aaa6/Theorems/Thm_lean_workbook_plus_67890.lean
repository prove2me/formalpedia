-- Prove2me | Theorems.Thm_lean_workbook_plus_67890
-- name    : lean_workbook_plus_67890
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/22318ffd-9ebf-4e27-b4c2-661d626e3597
-- statement:
--   $\implies b-a=1,2\implies \boxed{\boxed{\mid a-b\mid \le 2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67890 (a b : ℝ) (h₁ : b - a = 1 ∨ b - a = 2) : |a - b| ≤ 2   :=  by sorry
