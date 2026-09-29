-- Prove2me | Theorems.Thm_lean_workbook_plus_55463
-- name    : lean_workbook_plus_55463
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3b2b0437-d066-403e-b695-77b6eb37ad35
-- statement:
--   Determine if there exists an integer $n > 0$ such that $A^n = I$, where $A$ is a square matrix with 1s on the diagonal and 0s everywhere else, and $I$ is the identity matrix.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55463 (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.diag = 1 ∧ ∀ i j, i ≠ j → A i j = 0) : ∃ k : ℕ, A ^ k = 1   :=  by sorry
