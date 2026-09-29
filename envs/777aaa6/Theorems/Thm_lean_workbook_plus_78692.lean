-- Prove2me | Theorems.Thm_lean_workbook_plus_78692
-- name    : lean_workbook_plus_78692
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a764a0de-32e3-4cc8-a78c-5a9e3b661ee2
-- statement:
--   $f(n)=nf(1)-n+1 ,\quad \forall n \in \mathbb{N}_{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78692 (f : ℕ → ℕ) (hf: f = fun n => n * f 1 - n + 1) : ∀ n : ℕ, f n = n * f 1 - n + 1   :=  by sorry
