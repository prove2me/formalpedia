-- Prove2me | Theorems.Thm_lean_workbook_plus_14533
-- name    : lean_workbook_plus_14533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7c11aeaf-e570-4d48-aec1-25d866f5cd17
-- statement:
--   Let $ x;y;z$ be positive real numbers. Prove that: $(x+y+xy)(y+z+yz)(z+x+xz)\geq xyz(x+2)(y+2)(z+2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14533 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + x * y) * (y + z + y * z) * (z + x + z * x) ≥ x * y * z * (x + 2) * (y + 2) * (z + 2)   :=  by sorry
