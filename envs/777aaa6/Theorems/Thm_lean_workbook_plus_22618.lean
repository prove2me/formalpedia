-- Prove2me | Theorems.Thm_lean_workbook_plus_22618
-- name    : lean_workbook_plus_22618
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/640cec82-9c0d-43cd-9259-79c31dd04e76
-- statement:
--   I think that the following solution it is not ugly! Denote $x=sin^{2}a$ , $y=sin^{2}b$ , $z=sin^{2}c$ and we have $a,b,c\in\left[0,\frac{\pi}{2}\right].$ From the condition we got that $sin^{2}a\cdotp sin^{2}b\cdotp sin^{2}c=cos^{2}a\cdotp cos^{2}b\cdotp cos^{2}c$ ({*}). On the basis of my post #3 it is enought to prove that $sin^{2}a\cdotp sin^{2}b\cdotp sin^{2}c\leq\frac{1}{8}$ . We have the inequality betwen AM-GM: $\sqrt[3]{ABC}$ $\leq\frac{A+B+C}{3}$ . So we have $2\sqrt[3]{sin^{2}a\cdotp sin^{2}b\cdotp sin^{2}c}$ = $\sqrt[3]{sin^{2}a\cdotp sin^{2}b\cdotp sin^{2}c}+\sqrt[3]{cos^{2}a\cdotp cos^{2}b\cdotp cos^{2}c}$ $\leq$ , $\leq\frac{sin^{2}a+cos^{2}a+sin^{2}b+cos^{2}b+sin^{2}c+cos^{2}c}{3}$ =1 so $sin^{2}a\cdotp sin^{2}b\cdotp sin^{2}c\leq\frac{1}{8}$ q.e.d.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22618 :
  ∀ a b c : ℝ, a ∈ Set.Icc 0 (Real.pi / 2) ∧ b ∈ Set.Icc 0 (Real.pi / 2) ∧ c ∈ Set.Icc 0 (Real.pi / 2) ∧ a + b + c = π →
  sin a ^ 2 * sin b ^ 2 * sin c ^ 2 ≤ 1 / 8   :=  by sorry
