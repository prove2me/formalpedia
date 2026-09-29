-- Prove2me | Theorems.Thm_lean_workbook_plus_71000
-- name    : lean_workbook_plus_71000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9f07ec32-f7a5-4bb8-9057-53c20f0b8013
-- statement:
--   Prove that $a+b\ge 2\sqrt{ab}$ for all nonnegative $a,b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71000 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b ≥ 2 * Real.sqrt (a * b)   :=  by sorry
