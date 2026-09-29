-- Prove2me | Theorems.Thm_lean_workbook_plus_65368
-- name    : lean_workbook_plus_65368
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/21855f03-2fa1-4974-ae44-757b40fce005
-- statement:
--   For the second inequality Setting $a=x^2,b=y^2,c=z^2$ It is equivalent to $\sum{x^4}+\sum_{sym}{x^3y} +\sum{x^2yz} \geq 4\sum{x^2y^2}$ $\Leftrightarrow$ $\sum_{cyc}{(x^4+2x^3y-6x^2y^2+2xy^3+y^4)} +\sum_{cyc}{(-x^2y^2+2x^2yz-x^2z^2)} \geq 0$ $\Leftrightarrow$ $\sum_{cyc}{(x-y)^2(x^2+4xy+y^2-z^2)} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65368 :
  ∀ x y z : ℝ,
    (x - y) ^ 2 * (x ^ 2 + 4 * x * y + y ^ 2 - z ^ 2) +
    (y - z) ^ 2 * (y ^ 2 + 4 * y * z + z ^ 2 - x ^ 2) +
    (z - x) ^ 2 * (z ^ 2 + 4 * z * x + x ^ 2 - y ^ 2) ≥ 0   :=  by sorry
