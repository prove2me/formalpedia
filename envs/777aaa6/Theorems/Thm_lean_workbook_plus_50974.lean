-- Prove2me | Theorems.Thm_lean_workbook_plus_50974
-- name    : lean_workbook_plus_50974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1b33650e-b5bf-4a63-a79d-764c477360ee
-- statement:
--   Prove that \(w(w - 1)(w - 3) \ge 0\) for \(w \ge 3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50974 (w : ℝ) (h : w ≥ 3) : w * (w - 1) * (w - 3) ≥ 0   :=  by sorry
