-- Prove2me | Theorems.Thm_lean_workbook_plus_79331
-- name    : lean_workbook_plus_79331
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/fbadf486-da72-409a-b85f-bf74283cb55b
-- statement:
--   Let me try to word the question a little more clearly.\nLet $x$ and $y$ be positive integers, and let $t$ be the smallest positive integer such that $xt$ divides $y$ . Show that $t$ is a divisor of $y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79331 (x y : ℕ) (h₁ : 0 < x ∧ 0 < y) (h₂ : x * t ∣ y) : t ∣ y   :=  by sorry
