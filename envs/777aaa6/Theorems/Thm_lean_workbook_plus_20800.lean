-- Prove2me | Theorems.Thm_lean_workbook_plus_20800
-- name    : lean_workbook_plus_20800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/521b2438-f957-429c-bb3c-8019e5b20b39
-- statement:
--   Prove that \((2n+1)^{n+1}\leq(2n+1)!!3^n, \ \ \ \ \ \forall n \in \mathbb{N}, \ \ \ \ \ \ \ \ \ \ \ (*)\) where the equality holds only for \(n=1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20800 : ∀ n : ℕ, ((2 * n + 1) ^ (n + 1) ≤ (2 * n + 1)!! * 3 ^ n) ∧ (n = 1 ↔ (2 * n + 1) ^ (n + 1) = (2 * n + 1)!! * 3 ^ n)   :=  by sorry
