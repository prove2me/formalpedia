-- Prove2me | Theorems.Thm_lean_workbook_plus_54766
-- name    : lean_workbook_plus_54766
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3e0332d4-c194-444f-9aed-2c5632b30805
-- statement:
--   Define a function $f:A\to B$ where $A=\{1,2,3\}$ and $B=\{a,b,c\}$ such that $f$ is bijective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54766 (A B : Finset ℕ) (hA : A = {1, 2, 3}) (hB : B = {a, b, c}) : ∃ f : ℕ → ℕ, Function.Bijective f   :=  by sorry
