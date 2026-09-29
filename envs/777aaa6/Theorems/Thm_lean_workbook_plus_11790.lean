-- Prove2me | Theorems.Thm_lean_workbook_plus_11790
-- name    : lean_workbook_plus_11790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/64186107-aa28-4de6-bff7-2eace94cae2a
-- statement:
--   Given that $x+y+z=7$ , $xy+yz+xz=10$ and $xyz=5$ , compute $(2-x)(2-y)(2-z)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11790 (x y z : ℝ) (hx : x + y + z = 7) (hy : x*y + y*z + z*x = 10) (hz : x*y*z = 5) : (2 - x) * (2 - y) * (2 - z) = -5   :=  by sorry
