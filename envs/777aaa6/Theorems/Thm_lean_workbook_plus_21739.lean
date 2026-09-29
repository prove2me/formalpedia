-- Prove2me | Theorems.Thm_lean_workbook_plus_21739
-- name    : lean_workbook_plus_21739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ba542743-4b69-4ef6-b054-da8777a894a7
-- statement:
--   Prove the continuity of the exponential function $e^x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21739 : ∀ x : ℝ, ContinuousAt (fun x => exp x) x   :=  by sorry
