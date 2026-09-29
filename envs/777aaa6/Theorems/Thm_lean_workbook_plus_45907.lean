-- Prove2me | Theorems.Thm_lean_workbook_plus_45907
-- name    : lean_workbook_plus_45907
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8924db1a-7a0a-4b04-93a8-d20b51667f9e
-- statement:
--   $ \iff $ $2\cos 2x=\sin x\cos 2x+\sqrt 3\cos 2x\cos x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45907 (x : ℝ) : 2 * Real.cos 2 * x = Real.sin x * Real.cos 2 * x + Real.sqrt 3 * Real.cos 2 * x * Real.cos x ↔ 2 * Real.cos 2 * x = Real.sin x * Real.cos 2 * x + Real.sqrt 3 * Real.cos 2 * x * Real.cos x   :=  by sorry
