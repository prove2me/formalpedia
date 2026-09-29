-- Prove2me | Theorems.Thm_lean_workbook_plus_78080
-- name    : lean_workbook_plus_78080
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c3f3bd9d-18bd-4fec-bb0c-4f5fe835d151
-- statement:
--   Multiply hung's $\sum_{cyc}\frac{ab(a+b)}{c^2} \ge 2(a+b+c)$ by $a^2b^2c^2$ to obtain $\sum_{sym}a^3b^4\ge\sum_{sym}a^3b^2c^2$ \n\n<=> $\sum a^3(b^2-c^2)^2\ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78080 : ∀ a b c : ℝ, (a^3 * (b^2 - c^2)^2 + b^3 * (c^2 - a^2)^2 + c^3 * (a^2 - b^2)^2 ≥ 0)   :=  by sorry
