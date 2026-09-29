-- Prove2me | Theorems.Thm_lean_workbook_plus_54020
-- name    : lean_workbook_plus_54020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/21439560-f875-4669-ac65-74b2515d6640
-- statement:
--   By Titu's lemma,\n$\frac{a^2}{x}+\frac{b^2}{y}+\frac{c^2}{z}\ge \frac{(a+b+c)^2}{x+y+z}$ .......(2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54020 (x y z a b c : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (a^2 / x + b^2 / y + c^2 / z) ≥ (a + b + c)^2 / (x + y + z)   :=  by sorry
