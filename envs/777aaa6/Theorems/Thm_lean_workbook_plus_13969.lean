-- Prove2me | Theorems.Thm_lean_workbook_plus_13969
-- name    : lean_workbook_plus_13969
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b3c99f4a-713d-42a4-a1cb-a713c89528af
-- statement:
--   Find $c_{1}y_{1}+c_{2}y_{2}$ where $y_{1}= \frac{5x-6}{25}$, $y_{2}= \frac{5x-6}{25}$, $c_{1}=-1$, and $c_{2}= 1$. Is $-1\cdot y_{1}+1\cdot y_{2}= 0$ a solution?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13969 (x : ℝ) : (-1 * (5 * x - 6) / 25) + (1 * (5 * x - 6) / 25) = 0   :=  by sorry
