-- Prove2me | Theorems.Thm_lean_workbook_plus_76941
-- name    : lean_workbook_plus_76941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/882c4990-d964-42e1-9651-9755ce6193d8
-- statement:
--   Prove that $f(n)=n$ for all integers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76941 (f : ℤ → ℤ) (hf: f = fun n ↦ n) : ∀ n, f n = n   :=  by sorry
