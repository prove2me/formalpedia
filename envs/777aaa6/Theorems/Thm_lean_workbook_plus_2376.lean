-- Prove2me | Theorems.Thm_lean_workbook_plus_2376
-- name    : lean_workbook_plus_2376
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/836b4609-9f61-46c5-8b3d-2a577e4d82d1
-- statement:
--   Solve $d=rt=15(3-x)=3x$ Answer is $x=2.5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2376 (x d r t : ℝ) : d = r * t ∧ d = 15 * (3 - x) ∧ d = 3 * x → x = 2.5   :=  by sorry
