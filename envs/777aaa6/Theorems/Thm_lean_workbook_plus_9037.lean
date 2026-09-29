-- Prove2me | Theorems.Thm_lean_workbook_plus_9037
-- name    : lean_workbook_plus_9037
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/51d2ccd9-03ec-4cd1-8a2d-f201a738a662
-- statement:
--   There are $\binom{10}{2}$ ways to choose the values of $a$ and $b$ , and $\binom{4}{2}$ ways to choose the slips of each of those numbers. Thus there are $\binom{10}{2}\binom{4}{2}\binom{4}{2}=1620$ ways that two of the slips bear a number $a$ and the other two bear a number $b\not = a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9037 :
  10! / (8! * 2!) * (4! / (2! * 2!)) * (4! / (2! * 2!)) = 1620   :=  by sorry
