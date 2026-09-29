-- Prove2me | Theorems.Thm_lean_workbook_plus_67533
-- name    : lean_workbook_plus_67533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/2ae65299-af38-4732-8045-8c4899b40dd9
-- statement:
--   Determine all solutions $f: \mathbb{N} \to \mathbb{N}$ of the functional equation \n\n$f(n+m)=f(n)+f(m),$\n\nfor all $m,n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67533 (f : ℕ → ℕ): (∀ m n: ℕ, f (m + n) = f m + f n) ↔ ∃ a: ℕ, ∀ n: ℕ, f n = a * n   :=  by sorry
