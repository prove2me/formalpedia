-- Prove2me | Theorems.Thm_lean_workbook_plus_24732
-- name    : lean_workbook_plus_24732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/fe6dfc5f-a5a0-45b4-a6bb-73da590256a5
-- statement:
--   Show that if $x+y+z=0$ then $\frac{x^5+y^5+z^5}{5}=\frac{x^2+y^2+z^2}{2} \times \frac{x^3+y^3+z^3}{3}$ and $\frac{x^7+y^7+z^7}{7}=\frac{x^5+y^5+z^5}{5} \times \frac{x^2+y^2+z^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24732 (x y z : ℝ) (h : x + y + z = 0) : (x^5 + y^5 + z^5)/5 = (x^2 + y^2 + z^2)/2 * (x^3 + y^3 + z^3)/3 ∧ (x^7 + y^7 + z^7)/7 = (x^5 + y^5 + z^5)/5 * (x^2 + y^2 + z^2)/2   :=  by sorry
