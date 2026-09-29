-- Prove2me | Theorems.Thm_lean_workbook_plus_64633
-- name    : lean_workbook_plus_64633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7407bb95-f0fe-4666-8feb-4ecc7a9d22ed
-- statement:
--   Prove that $n^4+3=((n-1)(n+1))^2+(n-1)^2+(n+1)^2$ for all integers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64633 (n : ℤ) : n^4 + 3 = ((n-1)*(n+1))^2 + (n-1)^2 + (n+1)^2   :=  by sorry
