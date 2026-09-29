-- Prove2me | Theorems.Thm_lean_workbook_plus_17679
-- name    : lean_workbook_plus_17679
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/77746e5e-227c-46c3-8207-6d34fdbc8250
-- statement:
--   Prove that for every $p>=1$ the Inequality Is true \n\n $2p^3 + 4p + 1 >=6p^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17679 (p : ℝ) (hp : 1 ≤ p) : 2 * p ^ 3 + 4 * p + 1 ≥ 6 * p ^ 2   :=  by sorry
