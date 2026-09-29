-- Prove2me | Theorems.Thm_lean_workbook_plus_70207
-- name    : lean_workbook_plus_70207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/547aa4d4-4de6-4928-bc98-96a6c0805914
-- statement:
--   we have $ a\geq b+c $ ,but $ a=6-(b+c),$ so $ a\geq3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70207 (a b c : ℝ) (h₁ : a ≥ b + c) (h₂ : a = 6 - (b + c)) : a ≥ 3   :=  by sorry
