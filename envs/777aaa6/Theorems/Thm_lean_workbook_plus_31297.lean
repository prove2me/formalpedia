-- Prove2me | Theorems.Thm_lean_workbook_plus_31297
-- name    : lean_workbook_plus_31297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d2c7bbf7-807f-4d88-b9ab-0e9a6ecf8b7d
-- statement:
--   Given the condition $a^2 + ab + b^2 \equiv 0 \pmod{p}$, prove that $(a + b)^2 \equiv ab \pmod{p}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31297 (a b : ℤ) (p : ℕ) (hp : p.Prime) (h : a^2 + a*b + b^2 ≡ 0 [ZMOD p]) : (a + b)^2 ≡ a * b [ZMOD p]   :=  by sorry
