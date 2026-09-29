-- Prove2me | Theorems.Thm_lean_workbook_plus_68558
-- name    : lean_workbook_plus_68558
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c4423e47-f26d-4109-993b-876c556c1746
-- statement:
--   $\frac 1{10}-\frac 1{1001}<\sum_{i=10}^{1000}\frac 1{i^2}<\frac 19-\frac 1{1000}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68558 : (1 / 10 - 1 / 1001) < (∑ i in (Finset.Icc 10 1000), (1 / (i^2))) ∧ (∑ i in (Finset.Icc 10 1000), (1 / (i^2))) < (1 / 9 - 1 / 1000)   :=  by sorry
