-- Prove2me | Theorems.Thm_lean_workbook_plus_43824
-- name    : lean_workbook_plus_43824
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/28855fc5-8d0d-461c-b6c6-d21382e210e6
-- statement:
--   Prove that $(x+y+z)^2 \geq 3(xy+yz+zx)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43824 (x y z : ℝ) : (x+y+z)^2 >= 3*(x*y+y*z+z*x)   :=  by sorry
