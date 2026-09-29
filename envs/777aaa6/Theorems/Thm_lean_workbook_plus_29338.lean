-- Prove2me | Theorems.Thm_lean_workbook_plus_29338
-- name    : lean_workbook_plus_29338
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/efd8200d-7d77-4dce-920c-61cd92535301
-- statement:
--   Given $x = {a^{\frac{2}{3}}}, y = {b^{\frac{2}{3}}}, z = {c^{\frac{2}{3}}}$, prove from Shur inequality that $\sum\limits_{cyc} {{x^3}} + 3xyz \geqslant \sum\limits_{cyc} {xy(\underbrace {x + y}_{Am - Gm})} \geqslant 2\sum\limits_{cyc} {{{(xy)}^{\frac{3}{2}}}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29338 (x y z : ℝ) (hx : x = a^(2/3)) (hy : y = b^(2/3)) (hz : z = c^(2/3)) : x^3 + y^3 + z^3 + 3 * x * y * z ≥ x * y * (x + y) + y * z * (y + z) + z * x * (z + x) ∧ x * y * (x + y) + y * z * (y + z) + z * x * (z + x) ≥ 2 * (x * y)^(3 / 2) + 2 * (y * z)^(3 / 2) + 2 * (z * x)^(3 / 2)   :=  by sorry
