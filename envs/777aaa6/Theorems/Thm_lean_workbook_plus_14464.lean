-- Prove2me | Theorems.Thm_lean_workbook_plus_14464
-- name    : lean_workbook_plus_14464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/32f169f2-9970-498b-be00-66cf9013ab55
-- statement:
--   Prove that, if $u_{n+1} = u_{n} +2$ for $n \in \mathbb{N}$ and $u_{1}=3$ , then $u_{n}= 2n+1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14464 (n : ℕ) (u : ℕ → ℕ) (h₁ : u 1 = 3) (h₂ : ∀ n, u (n+1) = u n + 2) : u n = 2 * n + 1   :=  by sorry
