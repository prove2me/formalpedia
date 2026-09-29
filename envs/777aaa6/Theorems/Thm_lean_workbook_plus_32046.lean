-- Prove2me | Theorems.Thm_lean_workbook_plus_32046
-- name    : lean_workbook_plus_32046
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7ae173f0-4616-4616-9c80-0eca3f4b9d84
-- statement:
--   Prove that for $n \geq 1$, $\frac{(n)(n+1)(2n+1)}{6}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32046 (n : ℕ) (hn : 1 ≤ n) : ∃ k : ℤ, (n : ℤ) * (n + 1) * (2 * n + 1) / 6 = k   :=  by sorry
