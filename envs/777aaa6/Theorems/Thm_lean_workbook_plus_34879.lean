-- Prove2me | Theorems.Thm_lean_workbook_plus_34879
-- name    : lean_workbook_plus_34879
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a72ac7a3-a5a7-4ca4-980e-528fd9d1ef4f
-- statement:
--   Call the number of people at the funfair $x$ . \n\n $\dfrac{3}{8}x$ are children and so $\dfrac{5}{8}\cdot\dfrac{3}{4}=\dfrac{15}{32}x$ are men, which also means that $\dfrac{5}{8}\cdot\dfrac{1}{4}=\dfrac{5}{32}x$ of the remaining people are women. \n\nWe are given that $\dfrac{3}{8}x-\dfrac{5}{32}x=140$ . Using simple algebra, we get that $x=$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34879 (x : ℝ) (hx : x > 0) (h : 3/8 * x - 5/32 * x = 140) : x = 640   :=  by sorry
