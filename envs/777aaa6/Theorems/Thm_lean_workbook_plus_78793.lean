-- Prove2me | Theorems.Thm_lean_workbook_plus_78793
-- name    : lean_workbook_plus_78793
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/03551408-e320-41e1-abf4-08c1f74b52fd
-- statement:
--   Prove that for all non-negative real numbers $a,b,c$ we always have\n$ \frac{a(b+c-a)}{a^2+2bc}+\frac{b(c+a-b)}{b^2+2ca}+\frac{c(a+b-c)}{c^2+2ab} \ge 0. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78793 :  ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a * (b + c - a) / (a ^ 2 + 2 * b * c) + b * (c + a - b) / (b ^ 2 + 2 * c * a) + c * (a + b - c) / (c ^ 2 + 2 * a * b) ≥ 0   :=  by sorry
