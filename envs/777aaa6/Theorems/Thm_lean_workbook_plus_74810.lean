-- Prove2me | Theorems.Thm_lean_workbook_plus_74810
-- name    : lean_workbook_plus_74810
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2d2ba738-f930-49bf-91fa-0d7e713dda1a
-- statement:
--   Prove that for all positive integers $n$ , $\sqrt{n} + \sqrt{n+2} > 2\sqrt{n + 0.8}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74810 : ∀ n : ℕ, (Real.sqrt n + Real.sqrt (n + 2) : ℝ) > 2 * Real.sqrt (n + 0.8)   :=  by sorry
