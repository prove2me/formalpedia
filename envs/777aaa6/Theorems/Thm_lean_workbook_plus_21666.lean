-- Prove2me | Theorems.Thm_lean_workbook_plus_21666
-- name    : lean_workbook_plus_21666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8f63b113-92bb-4112-b885-a550673657e2
-- statement:
--   Note that for all $0\le y\le1$ , \n $$12 y^5 - 30 y^4 + 40 y^3 - 30 y^2 + 12 y + 3=5-2y^6+2(y-1)^6\ge3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21666 : ∀ y : ℝ, y ∈ Set.Icc 0 1 → 12*y^5 - 30*y^4 + 40*y^3 - 30*y^2 + 12*y + 3 ≥ 3   :=  by sorry
