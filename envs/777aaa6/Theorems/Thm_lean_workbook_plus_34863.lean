-- Prove2me | Theorems.Thm_lean_workbook_plus_34863
-- name    : lean_workbook_plus_34863
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9fc7e866-b877-42bd-abd5-028deaaadee5
-- statement:
--   For $n$ odd, show that $(4^n + 1)/5$ is divisible by 5.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34863 : ∀ n : ℕ, Odd n → 5 ∣ (4^n + 1) / 5   :=  by sorry
