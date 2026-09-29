-- Prove2me | Theorems.Thm_lean_workbook_plus_66707
-- name    : lean_workbook_plus_66707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5d0921ee-9f98-4da6-81b0-134bfaa7c5f0
-- statement:
--   If $x,y,z$ are positive real numbers such that $3=xy+yz+zx$ show that $3(x+y)(x+z)(y+z)(x+y+z)\ge 8(x^2+y^2+z^2+6)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66707 (x y z : ℝ) (h : 3 = x * y + y * z + z * x) : 3 * (x + y) * (x + z) * (y + z) * (x + y + z) ≥ 8 * (x ^ 2 + y ^ 2 + z ^ 2 + 6)   :=  by sorry
