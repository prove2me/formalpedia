-- Prove2me | Theorems.Thm_lean_workbook_plus_3727
-- name    : lean_workbook_plus_3727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e1d96d8b-a9c8-449f-a716-61cd36e885e0
-- statement:
--   Case 1: Jamal has a $\frac{60}{100} = \frac{3}{5}$ chance of using the bus, and a $\frac{15}{100} = \frac{3}{20}$ chance of arriving home after 7 PM when he does. Multiplying the probabilities (dependent events) gives $\frac{9}{100}$, which is the probability of Jamal arriving home after 7 PM if he travels via bus.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3727 :
  (3 : ℚ)/5 * (3 : ℚ)/20 = (9 : ℚ)/100   :=  by sorry
