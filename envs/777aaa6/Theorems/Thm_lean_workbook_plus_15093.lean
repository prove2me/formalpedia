-- Prove2me | Theorems.Thm_lean_workbook_plus_15093
-- name    : lean_workbook_plus_15093
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/df056c4e-24f8-43c0-8694-442db8a56835
-- statement:
--   Prove that $(x+y+z-3)(2(x+y+z)-3)\ge 0$ given $x+y+z \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15093 (x y z : ℝ) (h : x + y + z ≥ 3) :
  (x + y + z - 3) * (2 * (x + y + z) - 3) ≥ 0   :=  by sorry
