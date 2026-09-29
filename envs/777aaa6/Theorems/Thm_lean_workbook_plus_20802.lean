-- Prove2me | Theorems.Thm_lean_workbook_plus_20802
-- name    : lean_workbook_plus_20802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/353a26de-5d70-4e8d-8072-c897b28541a9
-- statement:
--   2) $f(1)=1$ and $\forall n\ge 2$ : $n\ge f(n)\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20802 (f : ℕ → ℕ) (hf: f 1 = 1 ∧ ∀ n ≥ 2, n ≥ f n ∧ f n ≥ 2) : ∃ n, n ≥ f n ∧ f n ≥ 2   :=  by sorry
