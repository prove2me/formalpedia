-- Prove2me | Theorems.Thm_lean_workbook_plus_62337
-- name    : lean_workbook_plus_62337
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6d003b64-a481-40e4-89d7-d10802707c31
-- statement:
--   $ \sin 2x = \sqrt{2} \cos x \iff 2 \sin x \cos x = \sqrt{2} \cos x. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62337 (x : ℝ) : sin (2 * x) = Real.sqrt 2 * cos x ↔ 2 * sin x * cos x = Real.sqrt 2 * cos x   :=  by sorry
