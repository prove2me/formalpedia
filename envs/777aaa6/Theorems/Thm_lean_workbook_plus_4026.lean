-- Prove2me | Theorems.Thm_lean_workbook_plus_4026
-- name    : lean_workbook_plus_4026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/80f74364-048c-41bd-b475-16445345aabf
-- statement:
--   For $x,y,z,t \in R$ prove that $2(x-y)(y-z)(z-t)(t-x)+(x-z)^2(y-t)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4026 (x y z t : ℝ) :
  2 * (x - y) * (y - z) * (z - t) * (t - x) + (x - z) ^ 2 * (y - t) ^ 2 ≥ 0   :=  by sorry
