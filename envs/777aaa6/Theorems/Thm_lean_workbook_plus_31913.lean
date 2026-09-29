-- Prove2me | Theorems.Thm_lean_workbook_plus_31913
-- name    : lean_workbook_plus_31913
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/dd70dfb4-d625-403e-8a18-c086516df5b2
-- statement:
--   In general if you have $a,b>0$ and you want to maximize $y=a\sin x +b\cos x$ you can simply use Cauchy-Schwarz: $y^2 \le (a^2+b^2)(\sin^2(x)+\cos^2(x))=a^2+b^2$ and so $y \le \sqrt{a^2+b^2}$ where the maximum is attained for $\tan x=\frac{\sin x}{\cos x}=\frac{a}{b}$ and so $x=\arctan \frac{a}{b}$ with $x \in [0, \frac{\pi}{2})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31913  (a b : ℝ)
  (x : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 ≤ x ∧ x < π / 2) :
  a * Real.sin x + b * Real.cos x ≤ Real.sqrt (a^2 + b^2)   :=  by sorry
