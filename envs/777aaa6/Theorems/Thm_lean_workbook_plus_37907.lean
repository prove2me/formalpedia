-- Prove2me | Theorems.Thm_lean_workbook_plus_37907
-- name    : lean_workbook_plus_37907
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/07dcc30c-6acc-49c0-a48f-1fbe1d73c3cf
-- statement:
--   Find the functions $f:\\mathbb{N}\\rightarrow \\mathbb{N}$ with satisfy:\n(i), $f(f(n))=n$\n(ii), $n|f(1)+f(2)+...+f(n)$\nfor every $n\\in \\mathbb{N}$ ($\\mathbb{N}$ is the set of all positive integers)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37907 (n : ℕ) (f : ℕ → ℕ) (hf: f (f n) = n) (h : n ∣ (Finset.sum (Finset.range n) f)) : f (f n) = n ∧ n ∣ (Finset.sum (Finset.range n) f)   :=  by sorry
