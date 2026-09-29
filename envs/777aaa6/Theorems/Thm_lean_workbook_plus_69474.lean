-- Prove2me | Theorems.Thm_lean_workbook_plus_69474
-- name    : lean_workbook_plus_69474
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/8cb8fc0e-6a5d-456f-8e63-a104b806e246
-- statement:
--   Prove, $\sum_{k=1}^{1008} \binom{2017}{k} k \equiv 0 \pmod{2017^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69474 (n : ℕ) : ∑ k in Finset.Icc 1 1008, (Nat.choose 2017 k * k) ≡ 0 [ZMOD 2017^2]   :=  by sorry
