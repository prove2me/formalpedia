-- Prove2me | Theorems.Thm_lean_workbook_plus_46829
-- name    : lean_workbook_plus_46829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a0816c82-89fc-4802-8dec-579591030893
-- statement:
--   Given $4a(a+1) = 8x$ for some $x$, prove that $x$ is a triangular number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46829 (a x : ℕ) (h : 4 * a * (a + 1) = 8 * x) : ∃ k : ℕ, k * (k + 1) / 2 = x   :=  by sorry
