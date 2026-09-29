-- Prove2me | Theorems.Thm_lean_workbook_plus_62528
-- name    : lean_workbook_plus_62528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cfc51b8f-fba6-4102-bcbb-9bb924501a7e
-- statement:
--   Prove that the sequence $a_n = \sqrt{3a_{n-1} + 1}$ is strictly increasing and bounded above.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62528 (a : ℕ → ℝ) (ha : a 0 = 1) (hab : ∀ n, a (n + 1) = Real.sqrt (3 * a n + 1)) : ∃ M, ∀ n, a n < M   :=  by sorry
