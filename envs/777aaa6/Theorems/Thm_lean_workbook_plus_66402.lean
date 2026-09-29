-- Prove2me | Theorems.Thm_lean_workbook_plus_66402
-- name    : lean_workbook_plus_66402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ad9a8a48-674f-4d84-af10-0ad40ec608e6
-- statement:
--   Prove that for $x+y=1$, $xy\le \frac{1}{4}$ using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66402 (x y : ℝ) (h : x + y = 1) : x * y ≤ 1 / 4   :=  by sorry
