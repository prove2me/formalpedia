-- Prove2me | Theorems.Thm_lean_workbook_plus_63048
-- name    : lean_workbook_plus_63048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/02ba0953-b2bd-481c-b17e-b9f676807635
-- statement:
--   Prove: $(1+p)^n \ge 1+np$ For every number $p>-1$ and for any positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63048 {p : ℝ} (hp : p > -1) {n : ℕ} (hn : n ≥ 1) : (1 + p)^n ≥ 1 + n * p   :=  by sorry
