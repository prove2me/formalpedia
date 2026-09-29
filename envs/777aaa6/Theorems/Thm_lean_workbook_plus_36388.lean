-- Prove2me | Theorems.Thm_lean_workbook_plus_36388
-- name    : lean_workbook_plus_36388
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/239c8cb1-bd58-4cea-bfff-f1782bf57f6b
-- statement:
--   Prove that $\sin(x + y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36388 (x y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y   :=  by sorry
