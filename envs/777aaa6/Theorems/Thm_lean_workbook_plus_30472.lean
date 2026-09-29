-- Prove2me | Theorems.Thm_lean_workbook_plus_30472
-- name    : lean_workbook_plus_30472
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b95f3c9b-4553-4e88-bf1d-ea9552929dbd
-- statement:
--   Let $ a,b,c $ be length-side of a triangle , and $ S $ be area , $ x,y,z$ are real numbers, Prove that:\n $x^2+y^2+z^2\ge4S\sqrt{\frac{y^2z^2}{b^2c^2}+\frac{z^2x^2}{c^2a^2}+\frac{x^2y^2}{a^2b^2}.}$\nIn particular， $a^2+b^2+c^2\ge4S\sqrt{\frac{a^2}{b^2}+\frac{b^2}{c^2}+\frac{c^2}{a^2}.}$\n $bc+ca+ab\ge4S\sqrt{\frac{a}{b}+\frac{b}{c}+\frac{c}{a}.}$\n\n<=>\n $\frac{1}{4}(x^2+y^2+z^2)^2 \geq y^2z^2\sin^2{A}+z^2x^2\sin^2{B}+x^2y^2\sin^2{C}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30472 : ∀ a b c S A : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧ A = arcsin (b * c / (a * Real.sqrt (a^2 + b^2 + c^2))) → ∀ x y z : ℝ, x^2 + y^2 + z^2 ≥ 4 * S * Real.sqrt (y^2 * z^2 / (b^2 * c^2) + z^2 * x^2 / (c^2 * a^2) + x^2 * y^2 / (a^2 * b^2))   :=  by sorry
