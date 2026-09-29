-- Prove2me | Theorems.Thm_lean_workbook_plus_6574
-- name    : lean_workbook_plus_6574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/15cb8bf1-b290-4c17-9db0-17aed970c49a
-- statement:
--   $\exists a,b\le \frac{p-1}{2} / 1+a(p-1)\equiv 1+b(p-1)\pmod{q}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6574 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ a b, a ≤ (p-1)/2 ∧ b ≤ (p-1)/2 ∧ 1 + a * (p-1) ≡ 1 + b * (p-1) [ZMOD q]   :=  by sorry
