-- Prove2me | Theorems.Thm_lean_workbook_plus_37242
-- name    : lean_workbook_plus_37242
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2446ae35-c2df-49bc-b3d7-e5812168350d
-- statement:
--   Prove that if $n$ is odd, then $5^n-1$ will never be divisible by $8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37242 (n : ℕ) (h : n % 2 = 1) : ¬ 8 ∣ (5^n - 1)   :=  by sorry
