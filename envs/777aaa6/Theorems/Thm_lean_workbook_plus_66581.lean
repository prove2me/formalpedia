-- Prove2me | Theorems.Thm_lean_workbook_plus_66581
-- name    : lean_workbook_plus_66581
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8f6a2978-dee2-4936-854f-8251aeae6c5a
-- statement:
--   Let $a,b,c >0$ and $a+b+c =3$. Prove that: $ab^2(b^2+1)+bc^2(c^2+1)+ca^2(a^2+1) \le 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66581 :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 → a * b ^ 2 * (b ^ 2 + 1) + b * c ^ 2 * (c ^ 2 + 1) + c * a ^ 2 * (a ^ 2 + 1) ≤ 6   :=  by sorry
