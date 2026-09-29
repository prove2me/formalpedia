-- Prove2me | Theorems.Thm_lean_workbook_plus_25724
-- name    : lean_workbook_plus_25724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/cd2f9947-acf3-420b-bd45-a12212e56a91
-- statement:
--   Does there exist a function $f:\mathbb{N}\to\mathbb{N}$ such that $f(2008)\not= 2008$ and $f(m+f(n))=f(f(m))+f(n)$ for all $m,n\in\mathbb{N}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25724 : ∃ f : ℕ → ℕ, f 2008 ≠ 2008 ∧ ∀ m n, f (m + f n) = f (f m) + f n   :=  by sorry
