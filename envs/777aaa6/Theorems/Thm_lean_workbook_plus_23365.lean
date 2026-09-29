-- Prove2me | Theorems.Thm_lean_workbook_plus_23365
-- name    : lean_workbook_plus_23365
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2142d0e2-df54-48f6-9bd1-7b6c5e5e0ed6
-- statement:
--   If $(a,b) =1$ there exists such $n$ that $an \equiv 1$ $(mod b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23365 {a b : ℕ} (hab : Nat.Coprime a b) : ∃ n, a*n ≡ 1 [ZMOD b]   :=  by sorry
