-- Prove2me | Theorems.Thm_lean_workbook_plus_38303
-- name    : lean_workbook_plus_38303
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/68f67225-2c69-4983-a8c0-e9aac07cc8e3
-- statement:
--   Let $p,q$ be rational numbers. Set $r=p+q\sqrt{7}$ . Prove that there exists intergers $a,b,c,d$ that satisfy: $ad-bc=1$ and $\frac{ar+b}{cr+d}=r$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38303 (p q : ℚ) (r : ℝ) (hr : r = p + q * Real.sqrt 7) : ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a * r + b) / (c * r + d) = r   :=  by sorry
