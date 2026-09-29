-- Prove2me | Theorems.Thm_lean_workbook_plus_75695
-- name    : lean_workbook_plus_75695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/55bafe93-18fe-4f5b-91de-715e48a0e844
-- statement:
--   Exemple of a such function : $ f(x) = 0$ if $ (x\in [0,1]\cap Q)$ (rational), $ \ f(x) = 1$ if $ x\in ([0,1] - Q)$ (irrational)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75695 : ∃ f : ℝ → ℝ, ∀ x ∈ Set.Icc 0 1, (x ∈ Set.Icc 0 1 ∩ Set.range ((↑) : ℚ → ℝ)) → f x = 0 ∧ (x ∈ Set.Icc 0 1 \ Set.range ((↑) : ℚ → ℝ)) → f x = 1   :=  by sorry
