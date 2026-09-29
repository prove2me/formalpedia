-- Prove2me | Theorems.Thm_lean_workbook_plus_21788
-- name    : lean_workbook_plus_21788
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2395e155-0ff2-4538-862c-17dec92146bb
-- statement:
--   For $x>0,$ we define $\ln x=\int_1^x\frac1t\,dt.$ This integral exists, since continuous functions on closed bounded intervals are (Riemann) integrable. By the fundamental theorem of calculus, $\frac{d}{dx}\ln x=\frac1x.$ We show based on this definition (it's not too hard) that $\ln(xy)=\ln x+\ln y.$ Since $\ln(2^n)=n\ln 2,$ the range of the function $\ln x$ for $x\in (0,\infty)$ is $(-\infty,\infty).$ Hence, the logarithm function has an inverse function defined on $\mathbb{R}$ that we call $e^x.$ This inherits the laws of exponents properties from those properties for the logarithm, and we know its derivative from the inverse function theorem.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21788  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y) :
  Real.log (x * y) = Real.log x + Real.log y   :=  by sorry
