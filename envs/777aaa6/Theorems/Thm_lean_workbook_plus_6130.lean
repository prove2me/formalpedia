-- Prove2me | Theorems.Thm_lean_workbook_plus_6130
-- name    : lean_workbook_plus_6130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0c06c2cf-d417-46a7-87d1-b21f54b4e24c
-- statement:
--   Prove that $17(x+y+z)^4-76(x+y+z)^2(xy+yz+zx)+4(x+y+z)xyz-24(x+y+z)(x^2y+y^2z+z^2x)+98(xy+yz+zx)^2\geq 0$ for $x,y,z \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6130 (x y z : ℝ) : 17 * (x + y + z) ^ 4 - 76 * (x + y + z) ^ 2 * (x * y + y * z + z * x) + 4 * (x + y + z) * x * y * z - 24 * (x + y + z) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) + 98 * (x * y + y * z + z * x) ^ 2 ≥ 0   :=  by sorry
