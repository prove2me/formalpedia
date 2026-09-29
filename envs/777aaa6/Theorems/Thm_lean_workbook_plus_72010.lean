-- Prove2me | Theorems.Thm_lean_workbook_plus_72010
-- name    : lean_workbook_plus_72010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/436c15d2-e8ba-4607-8d43-7efcb4d2291e
-- statement:
--   Find all triples of reals $(x,y,z)$ satisfying: \n\n $$\begin{cases} \frac{1}{3} \min \{x,y\} + \frac{2}{3} \max \{x,y\} = 2017 \ \frac{1}{3} \min \{y,z\} + \frac{2}{3} \max \{y,z\} = 2018 \ \frac{1}{3} \min \{z,x\} + \frac{2}{3} \max \{z,x\} = 2019 \end{cases}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72010 (x y z : ℝ) : (x = 2018 ∧ y = 2015 ∧ z = 2019.5) ↔ (1/3 * min x y + 2/3 * max x y = 2017 ∧ 1/3 * min y z + 2/3 * max y z = 2018 ∧ 1/3 * min z x + 2/3 * max z x = 2019)   :=  by sorry
