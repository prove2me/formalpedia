-- Prove2me | Theorems.Thm_lean_workbook_plus_61100
-- name    : lean_workbook_plus_61100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7a60d5c8-093f-42a9-9d3b-f6625470d693
-- statement:
--   If $ a$ is an even positive integer and $ A = 1 + a + a^2 + .... + a^n,n\in N^*$ is a perfect square. Prove that $ 8|a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61100 (a : ℕ) (ha : Even a) (n : ℕ) (hn : 0 < n) (hA: A = (∑ i in Finset.range (n+1), a^i)) : ∃ k:ℕ, A = k^2 → 8 ∣ a   :=  by sorry
