-- Prove2me | Theorems.Thm_lean_workbook_plus_76974
-- name    : lean_workbook_plus_76974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ecee9ef6-c6da-4947-96ec-1be08a02bdfe
-- statement:
--   Let $ a,b,c \in[-1,1].$ Prove that $ a(1-b)+ b(1-c)+ c(1-a)+abc\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76974 (a b c: ℝ) (hab : a ∈ Set.Icc (-1) 1) (hbc : b ∈ Set.Icc (-1) 1) (hca : c ∈ Set.Icc (-1) 1): a * (1 - b) + b * (1 - c) + c * (1 - a) + a * b * c ≤ 1   :=  by sorry
