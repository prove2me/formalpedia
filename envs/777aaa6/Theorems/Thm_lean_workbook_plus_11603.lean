-- Prove2me | Theorems.Thm_lean_workbook_plus_11603
-- name    : lean_workbook_plus_11603
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/37ec94c9-9ec8-46e9-9b3d-4bff290dec07
-- statement:
--   Prove that if $\phi(n) = n-1$ for $n > 1$, then $n$ is prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11603 (n : ℕ) (h : 1 < n) : φ n = n - 1 → n.Prime   :=  by sorry
