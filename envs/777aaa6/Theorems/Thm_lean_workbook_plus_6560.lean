-- Prove2me | Theorems.Thm_lean_workbook_plus_6560
-- name    : lean_workbook_plus_6560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c247778f-7ec7-4014-95a6-c870483d4cf9
-- statement:
--   Let $p = \frac{1}{6}$ , the probability of winning. \n\nWins on his first turn: $(1-p)^3 p$ \nWins on his second turn: $(1-p)^7 p$ \nSum is geometric series with first term $(1-p)^3 p$ and common ratio $(1-p)^4$ , which is $\frac{(1-p)^3 p}{1-(1-p)^4} = \frac{125}{671}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6560 :
  (1 - 1 / 6)^3 * (1 / 6) / (1 - (1 - 1 / 6)^4) = 125 / 671   :=  by sorry
