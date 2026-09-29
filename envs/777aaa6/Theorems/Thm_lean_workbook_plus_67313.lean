-- Prove2me | Theorems.Thm_lean_workbook_plus_67313
-- name    : lean_workbook_plus_67313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/47086a9e-8b9c-4c0a-bf0e-d656d596af7c
-- statement:
--   Given that for any odd integer, either $n+1$ or $n-1$ is divisible by 4, prove that $(n+1)(n-1)$ is divisible by 4
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67313 : ∀ n : ℤ, n % 2 = 1 → 4 ∣ (n + 1) * (n - 1)   :=  by sorry
