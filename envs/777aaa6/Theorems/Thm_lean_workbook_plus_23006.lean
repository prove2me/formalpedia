-- Prove2me | Theorems.Thm_lean_workbook_plus_23006
-- name    : lean_workbook_plus_23006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f049afab-7182-4810-9289-b94ce79fa3fa
-- statement:
--   Find all functions $f:\mathbb{N} \to\mathbb{N},$ such that $f(a+f(b))=f(a)+f(b)$ and $f(x)=x+c$ for when $c$ is a constant. $f(x) = 0$ is not a solution since $f: \mathbb N\to \mathbb N$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23006 (f : ℕ → ℕ) (hf1 : ∃ c, ∀ x, f x = x + c) (hf2 : ∀ a b, f (a + f b) = f a + f b) : ∃ c, ∀ x, f x = x + c   :=  by sorry
