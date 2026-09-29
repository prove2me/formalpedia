-- Prove2me | solution 1 for lean_workbook_plus_82811
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:53:59.719905+00:00
-- url     : https://prove2.me/submissions/8a0ca637-20ce-47a5-81f3-cca9d3bc9afc

import Mathlib.Tactic

theorem solution (x : ℝ) (P : ℝ → ℝ) (h₁ : P x = -x) : P x = -x := h₁
