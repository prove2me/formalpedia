-- Prove2me | Theorems.Thm_lean_workbook_plus_78552
-- name    : lean_workbook_plus_78552
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/21fa9229-ef24-47c1-922e-0ad830949552
-- statement:
--   Prove that $\sin{3x}=3\sin{x}-4\sin^3{x}$ using complex numbers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78552 (x : ℂ) : (Complex.sin (3 * x) = 3 * Complex.sin x - 4 * (Complex.sin x)^3)   :=  by sorry
