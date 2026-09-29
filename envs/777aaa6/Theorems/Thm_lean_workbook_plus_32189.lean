-- Prove2me | Theorems.Thm_lean_workbook_plus_32189
-- name    : lean_workbook_plus_32189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ea5889d3-d57f-4cc9-b8ce-08652c1561eb
-- statement:
--   Let $a$ , $b$ , and $d$ be positive integers. It is known that $a+b$ is divisible by $d$ and $a\cdot b$ is divisible by $d^2$ . Prove that both $a$ and $b$ are divisible by $d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32189 (a b d : ℕ) (hab : a * b > 0) (h : a + b > 0) (ha : d > 0) (hb : d^2 > 0) : a * b % d^2 = 0 ∧ a + b % d = 0 → a % d = 0 ∧ b % d = 0   :=  by sorry
