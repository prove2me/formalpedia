-- Prove2me | Theorems.Thm_lean_workbook_plus_71179
-- name    : lean_workbook_plus_71179
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/80d6c82b-dfd5-45f0-a4b8-5d4f21ab4f80
-- statement:
--   Let $P$ and $Q$ be sets and $f$ be a function from $P$ to $Q$. For every subset $X\subseteq Q$, define $f^{-1}(X)=\{x\in P \mid f(x)\in X\}$. Show that $f^{-1}(f(A))=A$ if and only if $f$ is one-to-one. This has to be taken with a universal quantifier for all $A\subseteq P$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71179 (f : P → Q) (h : ∀ A : Set P, f ⁻¹' (f '' A) = A) : Function.Injective f   :=  by sorry
