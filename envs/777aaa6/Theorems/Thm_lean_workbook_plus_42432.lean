-- Prove2me | Theorems.Thm_lean_workbook_plus_42432
-- name    : lean_workbook_plus_42432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/32df7ca2-7708-44ff-8d52-beb7d3fb290c
-- statement:
--   The probability that it is raining and three martians say it is (result and condition) equals $\frac{3}{10} \cdot \left(\frac{4}{5}\right)^3=\frac{3}{10} \cdot \frac{64}{125}=\frac{96}{625}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42432 :
  (3 / 10 * (4 / 5)^3) = 96 / 625   :=  by sorry
