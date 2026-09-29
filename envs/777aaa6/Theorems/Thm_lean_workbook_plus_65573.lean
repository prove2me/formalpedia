-- Prove2me | Theorems.Thm_lean_workbook_plus_65573
-- name    : lean_workbook_plus_65573
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/004b099e-2a7a-4034-889b-627266e2deea
-- statement:
--   Write $2^x = a$ , $5^x = b$ , $7^x = c$ . Equation becomes $a^4+b^4+c^4=abc(a+b+c)$ . $a$ , $b$ , $c$ are all positive real numbers, so by Muirhead's Inequality, $a^4+b^4+c^4=abc(a+b+c) \iff a=b=c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65573 : ∀ a b c x : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^4 + b^4 + c^4 = a * b * c * (a + b + c) ↔ a = b ∧ b = c ∧ c = x   :=  by sorry
