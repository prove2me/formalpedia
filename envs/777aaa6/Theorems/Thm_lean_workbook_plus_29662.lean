-- Prove2me | Theorems.Thm_lean_workbook_plus_29662
-- name    : lean_workbook_plus_29662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/66a386ed-8145-4097-9f3a-97171e31d783
-- statement:
--   Let $1\ge x\ge y\ge z\ge 0$ ,and $a=\sqrt{x-y} ,b=\sqrt{y-z}, c=\sqrt{x-z} $ , so $ a^2+b^2=c^2 ,$ and $ 0\le c \le1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29662 (x y z a b c: ℝ) (h₁ : 1 ≥ x ∧ x ≥ y ∧ y ≥ z ∧ z ≥ 0)(h₂ : a = Real.sqrt (x - y) ∧ b = Real.sqrt (y - z) ∧ c = Real.sqrt (x - z))(h₃ : a^2 + b^2 = c^2): 0 ≤ c ∧ c ≤ 1   :=  by sorry
