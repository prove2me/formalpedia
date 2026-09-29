-- Prove2me | Theorems.Thm_lean_workbook_plus_18867
-- name    : lean_workbook_plus_18867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c901ba9f-0ccb-4d94-8f01-e525ad4f4029
-- statement:
--   substitution $ a=x+y,b=y+z,c=z+x$ ( $ x,y,z>0$ )\n\nThe following inequality is equivalent to\n\n $ 2(x^2+5xy+y^2+5zx+5yz+z^2)(x^2-xy+y^2-zx-yz+z^2)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18867 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : 2 * (x^2 + 5 * x * y + y^2 + 5 * z * x + 5 * z * y + z^2) * (x^2 - x * y + y^2 - z * x - z * y + z^2) ≥ 0   :=  by sorry
