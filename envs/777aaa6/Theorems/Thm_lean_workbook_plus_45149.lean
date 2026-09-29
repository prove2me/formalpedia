-- Prove2me | Theorems.Thm_lean_workbook_plus_45149
-- name    : lean_workbook_plus_45149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d70f41f8-f0ca-4220-a8bc-c89efa800d4a
-- statement:
--   prove that: $a(a+b)+b(b+c)+c(c+a)\geq a^3+b^3+c^3$, where $a,b,c \in[1,2]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45149 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2): a * (a + b) + b * (b + c) + c * (c + a) ≥ a ^ 3 + b ^ 3 + c ^ 3   :=  by sorry
