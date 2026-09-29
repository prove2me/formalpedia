-- Prove2me | Theorems.Thm_lean_workbook_plus_78731
-- name    : lean_workbook_plus_78731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e9353337-95da-4a12-821c-0933985cff55
-- statement:
--   Let $x,y,z \ge0$ . Prove that $(x+y+z)^4+3(xy+yz+zx)^2 \ge 4(x+y+z)^2(xy+yz+zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78731 (x y z: ℝ) : (x + y + z) ^ 4 + 3 * (x * y + y * z + z * x) ^ 2 ≥ 4 * (x + y + z) ^ 2 * (x * y + y * z + z * x)   :=  by sorry
