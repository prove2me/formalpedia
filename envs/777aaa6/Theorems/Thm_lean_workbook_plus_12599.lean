-- Prove2me | Theorems.Thm_lean_workbook_plus_12599
-- name    : lean_workbook_plus_12599
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8ba384aa-6337-4222-9c42-a93d5240b19a
-- statement:
--   What is $ ( - 1)^1 + ( - 1)^2 + \cdots + ( - 1)^{2006}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12599 : ∑ k in Finset.Icc 1 2006, (-1 : ℤ)^k = 0   :=  by sorry
