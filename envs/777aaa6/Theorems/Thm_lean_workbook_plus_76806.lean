-- Prove2me | Theorems.Thm_lean_workbook_plus_76806
-- name    : lean_workbook_plus_76806
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b0062cc6-4f7c-4da9-a4d9-123f9f3f072c
-- statement:
--   Prove by induction that \(\frac {3}{1! + 2! + 3!} + \frac {4}{2! + 3! + 4!} + \cdots + \frac {n + 2}{n! + (n + 1)! + (n + 2)!} = \frac{1}{2}\left(1 - \frac {2}{(n + 2)!}\right)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76806 (n : ℕ) : (∑ k in Finset.Icc 1 n, ((k + 2) / (k! + (k + 1)! + (k + 2)!))) = 1 / 2 * (1 - 2 / (n + 2)!)   :=  by sorry
