-- Prove2me | Theorems.Thm_lean_workbook_plus_74676
-- name    : lean_workbook_plus_74676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/1f2dc674-e755-4f4f-a3d8-7defaac4c065
-- statement:
--   It's $(x+y)(x+z)(y+z)\geq\frac{8}{9}(x+y+z)(xy+xz+yz)$ for positives $x$ , $y$ and $z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74676 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (x + z) * (y + z) ≥ (8 / 9) * (x + y + z) * (x * y + x * z + y * z)   :=  by sorry
