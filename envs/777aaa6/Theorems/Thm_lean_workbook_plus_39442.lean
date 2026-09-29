-- Prove2me | Theorems.Thm_lean_workbook_plus_39442
-- name    : lean_workbook_plus_39442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/aa1d0521-3ccd-45be-82e5-f9b1087c6d9c
-- statement:
--   If $2x+4y=1$ , then prove that $x^2+y^2 \ge (1/20)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39442 (x y : ℝ) (h : 2*x + 4*y = 1) : x^2 + y^2 ≥ 1/20   :=  by sorry
