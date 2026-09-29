-- Prove2me | Theorems.Thm_lean_workbook_plus_33290
-- name    : lean_workbook_plus_33290
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/918b0e1f-9e70-4e97-ae01-76b315c18906
-- statement:
--   Prove that $\left|\max\left(a,b\right)-\max\left(c,d\right)\right| \leq \max\left(\left|a-c\right|,\left|b-d\right|\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33290 (a b c d : ℝ) :
  |max a b - max c d| ≤ max (|a - c|) (|b - d|)   :=  by sorry
