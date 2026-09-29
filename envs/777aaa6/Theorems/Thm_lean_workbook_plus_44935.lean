-- Prove2me | Theorems.Thm_lean_workbook_plus_44935
-- name    : lean_workbook_plus_44935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/0cd3ae0c-2d78-4ab7-b402-694adab5b2dd
-- statement:
--   Let $a,b,c$ be non negative real numbers satisfying $a+b^2+c=1$ . Prove that $ (1+a^2)(1+b^2)(1+c^2)\geq \frac{25}{16} $ Equality holds when $a=c=\frac{1}{2},b=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44935 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b^2 + c = 1) : (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 25 / 16 ∧ (a = 1 / 2 ∧ b = 0 ∧ c = 1 / 2) → (1 + a^2) * (1 + b^2) * (1 + c^2) = 25 / 16   :=  by sorry
