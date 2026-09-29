-- Prove2me | Theorems.Thm_lean_workbook_plus_36722
-- name    : lean_workbook_plus_36722
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9cc5e791-5bf6-497a-88f9-916c682f0003
-- statement:
--   Prove: $1-\cos x=2 \sin^2 \frac{x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36722 : 1 - Real.cos x = 2 * (Real.sin (x / 2)) ^ 2   :=  by sorry
