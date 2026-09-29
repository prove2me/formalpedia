-- Prove2me | Theorems.Thm_lean_workbook_plus_71479
-- name    : lean_workbook_plus_71479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/01be9885-e33c-4a15-82fa-2805385fcee7
-- statement:
--   Prove that $ \sin x + \cos x = \sqrt {2}\sin(\theta + \pi/4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71479 (x : ℝ) : Real.sin x + Real.cos x = Real.sqrt 2 * Real.sin (x + Real.pi / 4)   :=  by sorry
