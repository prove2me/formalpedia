-- Prove2me | Theorems.Thm_lean_workbook_plus_48606
-- name    : lean_workbook_plus_48606
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fa36ceba-3458-49b6-945b-11fb218f54df
-- statement:
--   $$\begin{array}{l} \,\,\,\,\,\,{p^2} + 5{r^2} \ge 16Rr\\ \Leftrightarrow {\left( {x + y + z} \right)^2} + \frac{{5xyz}}{{x + y + z}} \ge 16\sqrt {\frac{{xyz}}{{x + y + z}}} .\frac{{\left( {x + y} \right)\left( {y + z} \right)\left( {z + x} \right)}}{{4\sqrt {xyz\left( {x + y + z} \right)} }}\\ \Leftrightarrow {\left( {x + y + z} \right)^2} + \frac{{5xyz}}{{x + y + z}} \ge 4\frac{{\left( {x + y} \right)\left( {y + z} \right)\left( {z + x} \right)}}{{\left( {x + y + z} \right)}}\\ \Leftrightarrow {\left( {x + y + z} \right)^3} + 5xyz \ge 4\left( {x + y} \right)\left( {y + z} \right)\left( {z + x} \right)\\ \Leftrightarrow {x^3} + {y^3} + {z^3} + 3xyz \ge xy\left( {x + y} \right) + yz\left( {y + z} \right) + zx\left( {z + x} \right) \end{array}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48606 : ∀ x y z : ℝ, (x + y + z)^3 + 5 * x * y * z ≥ 4 * (x + y) * (y + z) * (z + x)   :=  by sorry
