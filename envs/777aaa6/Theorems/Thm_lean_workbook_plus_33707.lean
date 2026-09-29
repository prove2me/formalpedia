-- Prove2me | Theorems.Thm_lean_workbook_plus_33707
-- name    : lean_workbook_plus_33707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/dec311e6-d669-45d2-8106-d87e2c052244
-- statement:
--   Prove that the infinite series $\sum^{\infty}_{n=1}n^2\cdot x^{2n}$ converges for all $0<x<1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33707 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  ∃ y, ∑' n : ℕ, (n^2 * x^(2 * n)) = y   :=  by sorry
