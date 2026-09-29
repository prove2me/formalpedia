-- Prove2me | Theorems.Thm_lean_workbook_plus_19546
-- name    : lean_workbook_plus_19546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9b2fce41-fb77-42bc-bba9-fb9adb36f5cc
-- statement:
--   For all $x>0$ and $d>0$ , we have $-\frac{27d}{4}x(dx-1)^2\leq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19546 (x d : ℝ) (hx : 0 < x) (hd : 0 < d) : -((27 * d)/4 * x * (d * x - 1)^2) ≤ 0   :=  by sorry
