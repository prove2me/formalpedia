-- Prove2me | Theorems.Thm_lean_workbook_plus_34596
-- name    : lean_workbook_plus_34596
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/bc5cc4fc-92f4-4082-9854-a976fa1c4816
-- statement:
--   Prove or disprove that $P(x)=x^n-1$ is divisible by $Q(x)=x^m-1$ if $m|n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34596 (m n : ℕ) (hm : m ∣ n) (hn : n ≠ 0) : (X ^ n - 1) % (X ^ m - 1) = 0   :=  by sorry
