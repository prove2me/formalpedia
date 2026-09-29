-- Prove2me | Theorems.Thm_lean_workbook_plus_35263
-- name    : lean_workbook_plus_35263
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/5277cd10-28c7-4fa5-9e21-1cb4c8fcd57c
-- statement:
--   Find the expression for $S_n=I+A+A^2+A^3+\cdots+A^{n-1}$ where $A=\left[\begin{array}{cc}1 & 2\\3 & 4\end{array}\right]$ and $I$ is the identity matrix.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35263 (n : ℕ) (hn : n > 0) (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A =!![1, 2; 3, 4]) : ∃ (S : Matrix (Fin 2) (Fin 2) ℝ), S = ∑ i in Finset.range n, A ^ i   :=  by sorry
