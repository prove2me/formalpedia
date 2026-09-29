-- Prove2me | Theorems.Thm_lean_workbook_plus_33727
-- name    : lean_workbook_plus_33727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/369ab0d6-f898-4c39-b4eb-bdefac4699e2
-- statement:
--   Find all triples of real numbers $(x, y, z)$ that satisfy the system of equations\n\n $$\frac{1}{3} \min\{x,y\} + \frac{2}{3} \max\{x,y\} = 2017$$\n $$\frac{1}{3} \min\{y,z\} + \frac{2}{3} \max\{y,z\} = 2018$$\n $$\frac{1}{3} \min\{z,x\} + \frac{2}{3} \max\{z,x\} = 2019.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33727 (x y z : ℝ) : (x = 2018 ∧ y = 2015 ∧ z = 2019.5 ↔ 1/3 * min x y + 2/3 * max x y = 2017 ∧ 1/3 * min y z + 2/3 * max y z = 2018 ∧ 1/3 * min z x + 2/3 * max z x = 2019)   :=  by sorry
