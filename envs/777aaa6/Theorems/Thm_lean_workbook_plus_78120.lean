-- Prove2me | Theorems.Thm_lean_workbook_plus_78120
-- name    : lean_workbook_plus_78120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/20706a97-1191-445f-989b-f86aa465c4d3
-- statement:
--   Then we prove that : \n $ 4(x + y + z)^2 \geq 3[ (x + y + z)^2 + xy + yz + zx]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78120 (x y z: ℝ) : 4 * (x + y + z) ^ 2 ≥ 3 * ((x + y + z) ^ 2 + x * y + y * z + z * x)   :=  by sorry
