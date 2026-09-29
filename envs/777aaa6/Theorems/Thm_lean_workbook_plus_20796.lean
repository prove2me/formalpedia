-- Prove2me | Theorems.Thm_lean_workbook_plus_20796
-- name    : lean_workbook_plus_20796
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4d3f20b2-e7b6-43fe-a507-ba1929e4a0fa
-- statement:
--   Prove that for any real number $x$, if $\ [x]=z$, then $z\in Z,\ z\le x<z+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20796 (x : ℝ) (z : ℤ) : (z = ⌊x⌋) → z ≤ x ∧ x < z + 1   :=  by sorry
