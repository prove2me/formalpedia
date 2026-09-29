-- Prove2me | Theorems.Thm_lean_workbook_plus_28710
-- name    : lean_workbook_plus_28710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/91c28496-2849-41f3-a2e4-3cab76904bfc
-- statement:
--   Let $P$ and $Q$ be sets and $f$ be a function from $P$ to $Q$. For every subset $X\subseteq Q$, define $f^{-1}(X)=\{x\in P \mid f(x)\in X\}$. Show that $f(f^{-1}(B))=B$ if and only if $f$ is onto. This has to be taken with a universal quantifier for all $B\subseteq Q$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28710 (P Q : Type) (f : P → Q) (h : ∀ B : Set Q, f '' (f ⁻¹' B) = B) : ∀ y : Q, ∃ x : P, f x = y   :=  by sorry
