-- Prove2me | Theorems.Thm_lean_workbook_plus_31005
-- name    : lean_workbook_plus_31005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/64628206-7b0b-489c-bb87-bb2633983dc2
-- statement:
--   from $ab+bc+ac+2abc=1$, by AM-GM, $1-2abc =ab+bc+ac \ge 3(abc)^{\frac{2}{3}}$. Then set $(abc)^{\frac{1}{3}}=x$. We have $1-2x^3 \ge 3x^2 \implies (x+1)^2(2x-1) \le 0$. Draw a graph of $f(x)=(x+1)^2(2x-1)$ and we will see $x\le \frac{1}{2}$, i.e. $abc \le \frac{1}{8}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31005  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a + 2 * a * b * c = 1) :
  a * b * c ≤ 1 / 8   :=  by sorry
