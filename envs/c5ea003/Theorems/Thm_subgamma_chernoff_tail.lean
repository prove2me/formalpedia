-- Prove2me | Theorems.Thm_subgamma_chernoff_tail
-- name    : subgamma_chernoff_tail
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T23:43:39.60046+00:00
-- url     : https://prove2.me/theorems/7b376c38-f665-47e2-b2bc-024ea8e9094f
-- title:
--   Sub-gamma Chernoff bound gives a Bennett–Bernstein tail
-- statement:
--   Sub-gamma Chernoff / Bennett–Bernstein tail: if a centered variable $Y$ has, for every $t\in[0,3)$, a sub-gamma MGF $\mathrm{mgf}_Y(t) \le \exp((e^t-1-t)v)$ with variance proxy $v>0$, then for $x>0$, $\mathbb{P}(Y \ge x) \le \exp\!\big(-x^2/(2(v+x/3))\big)$. The reusable concentration brick turning a sub-gamma MGF bound (entropy-method / modified-LSI output) into the closed-form Bennett–Bernstein deviation tail.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013) §2.4 Thm 2.10; Klein–Rio 2005 Ann.Probab.33 Thm 1.1(c) (arXiv:math/0506594); Bousquet 2002 C.R.Acad.Sci.334.

import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
open Real MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem subgamma_chernoff_tail
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (v x : ℝ) (hv : 0 < v) (hx : 0 < x)
    (hint : ∀ t : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hsg : ∀ t : ℝ, 0 ≤ t → t < 3 → ProbabilityTheory.mgf Y μ t ≤ Real.exp ((Real.exp t - 1 - t) * v)) :
    μ.real {ω | x ≤ Y ω} ≤ Real.exp (- x ^ 2 / (2 * (v + x / 3))) := by sorry
