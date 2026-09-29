-- Prove2me | Theorems.Thm_lean_workbook_plus_19303
-- name    : lean_workbook_plus_19303
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/477ee54d-9da8-406c-8a81-7ef90744eb11
-- statement:
--   Notice that $(x + y)(y + z)(z + x) = (x + y + z)(xy + yz + zx) - xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19303 (x y z : ℤ) : (x + y) * (y + z) * (z + x) = (x + y + z) * (x*y + y*z + z*x) - x*y*z   :=  by sorry
