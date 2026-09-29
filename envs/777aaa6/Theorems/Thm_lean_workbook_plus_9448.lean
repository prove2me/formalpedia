-- Prove2me | Theorems.Thm_lean_workbook_plus_9448
-- name    : lean_workbook_plus_9448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a19f7038-4624-4228-9341-a34612413f96
-- statement:
--   $21+4(xy+yz+zx)+3(x^2+y^2+z^2) \geq 14(x+y+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9448 (x y z : ℝ) : 21 + 4 * (x * y + y * z + z * x) + 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 14 * (x + y + z)   :=  by sorry
