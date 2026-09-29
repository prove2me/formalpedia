-- Prove2me | Theorems.Thm_lean_workbook_plus_48715
-- name    : lean_workbook_plus_48715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fb917b78-279d-4a13-8c72-e61d3a5d7a92
-- statement:
--   Prove that for $a,b,c$ such that $a+b+c=0$, we have: $\frac {x^2+y^2 + y^2} 2 \cdot \frac {x^3 + y^3 + z^3} 3 = \frac {x^5 + y^5 + z^5}5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48715 (x y z : ℝ) (h : x + y + z = 0) : (x^2 + y^2 + z^2) / 2 * (x^3 + y^3 + z^3) / 3 = (x^5 + y^5 + z^5) / 5   :=  by sorry
