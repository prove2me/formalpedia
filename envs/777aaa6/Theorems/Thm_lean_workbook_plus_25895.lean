-- Prove2me | Theorems.Thm_lean_workbook_plus_25895
-- name    : lean_workbook_plus_25895
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bdae1187-3ea3-4b55-809e-83be3c57be82
-- statement:
--   $ cosx-cosy=\frac{1}{5} $ $\implies{-2 \sin \frac{x+y}{2} \sin \frac{x-y}{2}=\frac{1}{5} }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25895 (x y : ℝ) (h : cos x - cos y = 1 / 5) :
  -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 1 / 5   :=  by sorry
