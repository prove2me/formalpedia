-- Prove2me | Theorems.Thm_lean_workbook_plus_69264
-- name    : lean_workbook_plus_69264
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5ea9edcb-4386-4eb6-b979-713dc8cb4ff7
-- statement:
--   Say the probability of rolling a $1$ is 1/21. The probability of getting 2 is $\frac{2}{21}$ and so on. The pairs that add up to 7 are $(1,6),(2,5),(3,4),(4,3),(5,2),(6,1)$ The probability of rolling $(1,6)$ is $\frac{1}{21}\cdot\frac{6}{21}$ . Doing this for all of them and then adding them up we get $\frac{1}{21}\cdot\frac{6}{21}+\frac{2}{21}\cdot\frac{5}{21}+\frac{3}{21}\cdot\frac{4}{21}+\frac{4}{21}\cdot\frac{3}{21}+\frac{5}{21}\cdot\frac{2}{21}+\frac{6}{21}\cdot\frac{1}{21}=\boxed{\frac{8}{63}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69264 :
  (1 / 21 * 6 / 21 + 2 / 21 * 5 / 21 + 3 / 21 * 4 / 21 + 4 / 21 * 3 / 21 + 5 / 21 * 2 / 21 + 6 / 21 * 1 / 21) = 8 / 63   :=  by sorry
