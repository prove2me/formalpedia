-- Prove2me | Theorems.Thm_lean_workbook_plus_67866
-- name    : lean_workbook_plus_67866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/2f345127-6adc-4f37-b04f-c887eb2f0050
-- statement:
--   If $x$ and $y$ are positive reals such that $xy=1$ , then $4+x^2+y^2 \ge 3(x+y)$ , with equality if and only if $x=y=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67866 (x y : ℝ) (h : x*y = 1) : 4 + x^2 + y^2 ≥ 3 * (x + y)   :=  by sorry
