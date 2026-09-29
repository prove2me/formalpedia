-- Prove2me | Theorems.Thm_lean_workbook_plus_73342
-- name    : lean_workbook_plus_73342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c82ced0a-b2b8-41e8-a37f-1117c5ad9736
-- statement:
--   (x+y)(y+z)(z+t)(t+x) \geq (x+y+z+t)(xyz+yzt+ztx+txy), where $x, y, z, t > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73342 {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : (x + y) * (y + z) * (z + t) * (t + x) ≥ (x + y + z + t) * (x * y * z + y * z * t + z * t * x + t * x * y)   :=  by sorry
