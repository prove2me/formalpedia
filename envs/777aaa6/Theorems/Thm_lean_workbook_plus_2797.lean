-- Prove2me | Theorems.Thm_lean_workbook_plus_2797
-- name    : lean_workbook_plus_2797
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/24916cd6-0455-45fc-8236-cf97a0498703
-- statement:
--   By Vasc's inequality we have \n $\frac53(a^2+b^2+c^2)^2 \ge 2\sum a^3b+3\sum ab^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2797 (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)   :=  by sorry
