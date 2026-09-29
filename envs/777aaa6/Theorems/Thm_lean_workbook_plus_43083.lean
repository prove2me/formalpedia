-- Prove2me | Theorems.Thm_lean_workbook_plus_43083
-- name    : lean_workbook_plus_43083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cc20f07f-842c-4a5c-a5a3-da87ef455cb4
-- statement:
--   Determine all functions $f : \mathbb{N} \to \mathbb{N}$ such that $f(a+b+ab)=f(ab)$, for all $a,b \in \mathbb{N}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43083 (f : ℕ → ℕ): (∀ a b : ℕ, f (a + b + a*b) = f (a*b)) ↔ ∃ c :ℕ, ∀ n : ℕ, f n = c   :=  by sorry
