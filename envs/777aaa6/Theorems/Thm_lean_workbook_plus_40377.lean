-- Prove2me | Theorems.Thm_lean_workbook_plus_40377
-- name    : lean_workbook_plus_40377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b262bbf4-665d-4eed-8822-330797e45746
-- statement:
--   Let $ a$ and $ b$ be integers. Prove that if a prime $ p$ divides $ ab$ , then $ p$ divides either $ a$ or $ b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40377 {a b : ℤ} {p : ℕ} (hp : p.Prime) (h : (p : ℤ) ∣ (a * b)) : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b   :=  by sorry
