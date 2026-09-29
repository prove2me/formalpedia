-- Prove2me | Theorems.Thm_lean_workbook_plus_53160
-- name    : lean_workbook_plus_53160
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5ae0e72c-4e94-4d11-9065-568d6fd682b5
-- statement:
--   Calculate $\sum_{k=0}^{10} 2^k \binom{10}{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53160 (h₁ : 0 < 10) : ∑ k in Finset.range 11, 2^k * (Nat.choose 10 k) = 59049   :=  by sorry
