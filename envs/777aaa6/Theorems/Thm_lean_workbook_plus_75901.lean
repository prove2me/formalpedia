-- Prove2me | Theorems.Thm_lean_workbook_plus_75901
-- name    : lean_workbook_plus_75901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d9d8515e-c55b-43fa-88a5-ef8ee7d4b03e
-- statement:
--   Does $ \displaystyle\sum_{j = 1}^n \displaystyle\sum_{i = 1}^m a_{ij}=\displaystyle\sum_{i = 1}^m \displaystyle\sum_{j = 1}^n a_{ij}$ hold for all n,m when $ a_{ij}\geq0 \ \forall i,j$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75901 (m n : ℕ) (a : Fin m → Fin n → NNReal) : ∑ j : Fin n, ∑ i : Fin m, a i j = ∑ i : Fin m, ∑ j : Fin n, a i j   :=  by sorry
