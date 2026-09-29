-- Prove2me | Theorems.Thm_lean_workbook_plus_20174
-- name    : lean_workbook_plus_20174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/2b0cd7db-0a99-41f3-a2d8-19dd097b4af5
-- statement:
--   $a(-b)=-(ab)=(-a)b ,and (-a)(-b)=ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20174 : ∀ a b : ℤ, a * (-b) = -(a * b) ∧ (-a) * b = -(a * b) ∧ (-a) * (-b) = a * b   :=  by sorry
