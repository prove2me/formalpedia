-- Prove2me | Theorems.Thm_lean_workbook_plus_74344
-- name    : lean_workbook_plus_74344
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a3ca5a0c-fe4c-443d-aa1e-5d1d3fdb72fc
-- statement:
--   Prove that if $P(x)$ is a non-constant polynomial with real coefficients and $P(x) = 0$ for all $x \in \mathbb{R}$, then all its coefficients are zero.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74344 (P : Polynomial ℝ) (hP : P ≠ 0) (h : ∀ x, P.eval x = 0) : P = 0   :=  by sorry
