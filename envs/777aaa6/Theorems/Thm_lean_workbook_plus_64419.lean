-- Prove2me | Theorems.Thm_lean_workbook_plus_64419
-- name    : lean_workbook_plus_64419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/21a31ed0-ec16-4f04-a653-a7ff7a6a29a2
-- statement:
--   Prove that $\cos(a+b) \sin(a-b) + \cos (b+c) \sin (b-c) + \cos (c+d) \sin (c-d) + \cos (d+a) \sin (d-a) =0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64419 (a b c d : ℝ) : cos (a + b) * sin (a - b) + cos (b + c) * sin (b - c) + cos (c + d) * sin (c - d) + cos (d + a) * sin (d - a) = 0   :=  by sorry
