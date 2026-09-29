-- Prove2me | Theorems.Thm_lean_workbook_plus_70834
-- name    : lean_workbook_plus_70834
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d23376d5-c747-4db8-824b-40751d91d71c
-- statement:
--   Prove that $\frac{1}{x+y+z+t^2}+\frac{1}{x+y+z^2+t}+\frac{1}{x+y^2+z+t}+\frac{1}{x^2+y+z+t}\le\frac{1}{4+t^2-t}+\frac{1}{4-z+z^2}+\frac{1}{4-y+y^2}+\frac{1}{x^2+4-x}$ given $x,y,z,t$ are positive numbers such that $x+y+z+t\ge4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70834 (x y z t : ℝ) (h : x + y + z + t ≥ 4) : 1 / (x + y + z + t ^ 2) + 1 / (x + y + z ^ 2 + t) + 1 / (x + y ^ 2 + z + t) + 1 / (x ^ 2 + y + z + t) ≤ 1 / (4 + t ^ 2 - t) + 1 / (4 - z + z ^ 2) + 1 / (4 - y + y ^ 2) + 1 / (x ^ 2 + 4 - x)   :=  by sorry
