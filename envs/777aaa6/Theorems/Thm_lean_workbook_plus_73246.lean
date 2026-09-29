-- Prove2me | Theorems.Thm_lean_workbook_plus_73246
-- name    : lean_workbook_plus_73246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8b050f68-86b9-4a87-9315-6c22c6d9ff96
-- statement:
--   Sea $f$ una funcion definida en $\mathbb{Z}^+$ por: $f(1) = 1$, $f(2n+1) = f(2n) + 1$, $f(2n) = 3f(n)$. Encontrar el conjunto de valores que toma la funcion $f$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73246 (f : ℕ → ℕ) (hf: f 1 = 1 ∧ ∀ n:ℕ, f (2*n + 1) = f (2*n) + 1 ∧ f (2*n) = 3 * f n) : ∃ A: Set ℕ, A = {n:ℕ | ∃ k:ℕ, n = f k}   :=  by sorry
