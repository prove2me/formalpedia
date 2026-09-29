-- Prove2me | Theorems.Thm_lean_workbook_plus_40440
-- name    : lean_workbook_plus_40440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ee9aecfd-99f2-4099-96f1-4905331a0178
-- statement:
--   If $x^2=y^2=1$ , then $(xy)^2=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40440 (x y : ℤ) (hx : x^2 = 1) (hy : y^2 = 1) : (x * y)^2 = 1   :=  by sorry
