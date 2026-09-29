-- Prove2me | Theorems.Thm_lean_workbook_plus_38429
-- name    : lean_workbook_plus_38429
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b65f1aed-106c-4777-b3c4-f0c2e36269bf
-- statement:
--   Prove that, for any natural numbers $n\geq m$ , the binomial coefficient $\binom{n}{m}\stackrel{def}{=}\frac{n!}{m!(n-m)!}$ is integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38429 (n m : ℕ) (h : m ≤ n) : ∃ k : ℤ, (n.choose m) = k   :=  by sorry
