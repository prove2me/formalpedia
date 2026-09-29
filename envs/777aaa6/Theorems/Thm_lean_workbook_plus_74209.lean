-- Prove2me | Theorems.Thm_lean_workbook_plus_74209
-- name    : lean_workbook_plus_74209
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b646ac6c-0c23-4b77-8cad-e50ff79747cf
-- statement:
--   Prove that $a^2 +b^2 + c^2 + ab + ac + bc \geq 6$ using the fact that $a+b+c=3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74209 (a b c : ℝ) (ha : a + b + c = 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6   :=  by sorry
