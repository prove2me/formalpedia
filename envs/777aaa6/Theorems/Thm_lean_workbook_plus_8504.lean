-- Prove2me | Theorems.Thm_lean_workbook_plus_8504
-- name    : lean_workbook_plus_8504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1ca75c39-bcda-4205-8ae8-1773a340dc9a
-- statement:
--   Prove that if $f(x)\equiv 1$, then $f(f(a))=f(1)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8504 (f : ℕ → ℕ) (a : ℕ) (h₁ : ∀ x, f x = 1) : f (f a) = 1   :=  by sorry
