-- Prove2me | Theorems.Thm_lean_workbook_plus_6174
-- name    : lean_workbook_plus_6174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7e670f4a-4665-472e-8805-3e931795d59a
-- statement:
--   PP. Let $a$ , $b$ , $c \in R^{+}$ . Solve the equation $\sqrt{a+bx}+\sqrt{b+cx}+\sqrt{c+ax}=\sqrt{b-ax}+\sqrt{c-bx}+\sqrt{a-cx}$ .\n\nProof. $f(x)=\left(\sqrt{a+bx}+\sqrt{b+cx}+\sqrt{c+ax}\right)-\left(\sqrt{b-ax}+\sqrt{c-bx}+\sqrt{a-cx}\right)$ is (strict) increasing $\left(\nearrow\right)$ . Equation\n\nbecomes $f(x)=0$ , where $f$ is injectively. Hence $f(x)=0$ has at most one zero. Since $f(0)=0$ obtain $x=0$ is alone zero.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6174  (a b c x : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 0 < x)
  (h₂ : Real.sqrt (a + b * x) + Real.sqrt (b + c * x) + Real.sqrt (c + a * x) = Real.sqrt (b - a * x) + Real.sqrt (c - b * x) + Real.sqrt (a - c * x)) :
  x = 0   :=  by sorry
