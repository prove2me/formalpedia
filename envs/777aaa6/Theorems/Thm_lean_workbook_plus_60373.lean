-- Prove2me | Theorems.Thm_lean_workbook_plus_60373
-- name    : lean_workbook_plus_60373
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/635658cf-553f-4c85-8583-ab8a7a3e1336
-- statement:
--   A pair of integers $(m,n)$ satisfies $m|n^2+1$ and $n|m^2+1$. Prove that there are an infinite number of these pairs and describe a set of such pairs.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60373 (m n : ℤ) (h₁ : m ∣ n^2 + 1) (h₂ : n ∣ m^2 + 1) : ∃ m n, (m ∣ n^2 + 1 ∧ n ∣ m^2 + 1) ∧ (m > n)   :=  by sorry
