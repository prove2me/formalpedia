-- Prove2me | Theorems.Thm_lean_workbook_plus_61538
-- name    : lean_workbook_plus_61538
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/28434a7c-43cf-4594-97d7-4c1883c2dc6c
-- statement:
--   Since \n\n $R^2=\frac{a^2b^2c^2}{16S^2}=\frac {a^2b^2c^2}{2a^2b^2+2b^2c^2+2c^2a^2-a^4-b^4-c^4}$ , \nusing the substitution $a^2=\frac{y+z}{2}$ etc., the inequality \n\n $\displaystyle \frac{a^4+b^4+c^4}{a^2+b^2+c^2} \ge 3R^2$ \n\nbecomes as follows \n\n $xy(x-y)^2+yz(y-z)^2+zx(z-x)^2 \ge 0.$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61538 :
  ∀ x y z : ℝ,
    x * y * (x - y) ^ 2 + y * z * (y - z) ^ 2 + z * x * (z - x) ^ 2 ≥ 0   :=  by sorry
