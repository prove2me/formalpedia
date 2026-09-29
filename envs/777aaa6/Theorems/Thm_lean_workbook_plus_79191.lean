-- Prove2me | Theorems.Thm_lean_workbook_plus_79191
-- name    : lean_workbook_plus_79191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/26e9bc1a-8a83-4e05-9037-e7484fbbbcd5
-- statement:
--   Prove that $10^{n+1} + 10^n + 1$ is divisible by $3$ for $n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79191 (n : ℕ) : 3 ∣ 10^(n+1) + 10^n + 1   :=  by sorry
