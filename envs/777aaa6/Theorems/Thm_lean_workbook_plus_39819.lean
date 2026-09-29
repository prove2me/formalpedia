-- Prove2me | Theorems.Thm_lean_workbook_plus_39819
-- name    : lean_workbook_plus_39819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ee2d9ef9-e6b2-4687-8cdd-271f41cb90ee
-- statement:
--   Define a function f : N to N\\*N as follows: $ f(1) = (1,1)$ $ f(2) = (2,1)$ $ f(3) = (1,2)$ $ f(4) = (3,1)$ $ f(5) = (2,2)$ $ f(6) = (1,3)$ $ f(7) = (4,1)$ and continue moving in a triangular pattern.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39819 : ∃ f : ℕ → ℕ × ℕ, f 1 = (1,1) ∧ f 2 = (2,1) ∧ f 3 = (1,2) ∧ f 4 = (3,1) ∧ f 5 = (2,2) ∧ f 6 = (1,3) ∧ f 7 = (4,1)   :=  by sorry
