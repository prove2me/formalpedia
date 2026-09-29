-- Prove2me | Theorems.Thm_lean_workbook_plus_10617
-- name    : lean_workbook_plus_10617
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1ecf1c1f-9721-46bb-b5cf-04c86d8c1653
-- statement:
--   Prove that the sum $1/2!+2/3!+3/4!+...+99/100!$ is equal to $1-\frac{1}{100!}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10617 : ∑ k in Finset.range 100, (k + 1) / (k + 2)! = 1 - 1 / 100!   :=  by sorry
