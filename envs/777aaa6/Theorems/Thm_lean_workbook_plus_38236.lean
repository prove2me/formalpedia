-- Prove2me | Theorems.Thm_lean_workbook_plus_38236
-- name    : lean_workbook_plus_38236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2e691f04-15d6-47a1-8e0f-78f5c91e30f8
-- statement:
--   Let A is associative ring in which \\(\\forall a\\in A\\) \\(a^2=0\\) and \\(\\forall n\\in\\mathbb N\\) \\(na=0\\Rightarrow a=0.\\) Prove that \\(abc=0,\\) where \\(a\\in A,\\) \\(b\\in A,\\) \\(c\\in A.\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38236 (A : Type*) [Ring A] (hA : ∀ a : A, a ^ 2 = 0) (hA' : ∀ n : ℕ, ∀ a : A, n * a = 0 → a = 0) (a b c : A) : a * b * c = 0   :=  by sorry
