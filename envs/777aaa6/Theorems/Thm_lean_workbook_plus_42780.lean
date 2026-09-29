-- Prove2me | Theorems.Thm_lean_workbook_plus_42780
-- name    : lean_workbook_plus_42780
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ded6eb6e-2656-4e50-b92e-2caffef77e5c
-- statement:
--   prove that \n\n $\cos 36 \sin 36 = \frac{\sin 72}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42780 : Real.cos (36 * Real.pi / 180) * Real.sin (36 * Real.pi / 180) = Real.sin (72 * Real.pi / 180) / 2   :=  by sorry
