-- Prove2me | Theorems.Thm_lean_workbook_plus_67748
-- name    : lean_workbook_plus_67748
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4269493b-4a21-47ba-8dcd-10d3ae5ce591
-- statement:
--   $ \sqrt{(a^2+d^2)(b^2+c^2)} \geq (ab+cd)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67748 (a b c d : ℝ) : Real.sqrt ((a^2 + d^2) * (b^2 + c^2)) ≥ a * b + c * d   :=  by sorry
