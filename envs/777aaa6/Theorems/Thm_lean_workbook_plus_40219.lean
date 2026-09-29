-- Prove2me | Theorems.Thm_lean_workbook_plus_40219
-- name    : lean_workbook_plus_40219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3deca73e-1045-4151-9f5a-bd9572a052ae
-- statement:
--   Prove: $\frac{xz}{(y+x)(y+z)}<\frac{xz}{xy+yz+zx}$ where $x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40219 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * z) / (y + x) / (y + z) < (x * z) / (x * y + y * z + z * x)   :=  by sorry
