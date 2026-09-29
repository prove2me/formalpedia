-- Prove2me | Theorems.Thm_lean_workbook_plus_25475
-- name    : lean_workbook_plus_25475
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1d131181-e691-48e1-8eea-98346930f19b
-- statement:
--   Given $xy=1$, prove that $(3+2xy)(18-6xy+x^2y^2)\leq 64$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25475 (x y : ℝ) (h : x * y = 1) :
  (3 + 2 * x * y) * (18 - 6 * x * y + x ^ 2 * y ^ 2) ≤ 64   :=  by sorry
