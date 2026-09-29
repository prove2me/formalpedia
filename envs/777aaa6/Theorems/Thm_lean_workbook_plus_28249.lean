-- Prove2me | Theorems.Thm_lean_workbook_plus_28249
-- name    : lean_workbook_plus_28249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fe38f0db-633b-4760-8125-f97b1a0cad18
-- statement:
--   Prove that $5^{n} -4n +15$ is divisible by $16$ for all integers $n \geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28249 (n : ℕ) (hn : 1 ≤ n) : 16 ∣ (5^n - 4*n + 15)   :=  by sorry
