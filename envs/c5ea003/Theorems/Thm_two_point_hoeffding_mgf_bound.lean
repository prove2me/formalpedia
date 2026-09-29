-- Prove2me | Theorems.Thm_two_point_hoeffding_mgf_bound
-- name    : two_point_hoeffding_mgf_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T00:19:38.652231+00:00
-- url     : https://prove2.me/theorems/2f6797ea-b2b6-4cb5-9bd4-fbb061953069
-- statement:
--   Two-point Hoeffding MGF inequality (Hoeffding 1963; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, Lemma 2.2). For a real number $p \in [0,1]$ and reals $a,b$, the two-point convex combination of exponentials is bounded by the exponential of the mean plus a Gaussian-type term: $p\,e^a + (1-p)\,e^b \le \exp\!\big(p a + (1-p) b + (a-b)^2/8\big)$. Equivalently, a two-point random variable taking value $a$ with probability $p$ and $b$ with probability $1-p$ has a sub-Gaussian MGF with variance proxy $(a-b)^2/4$.
-- source:
--   Hoeffding, W. (1963), Probability inequalities for sums of bounded random variables, JASA 58(301):13-30; Boucheron, Lugosi, Massart, Concentration Inequalities, OUP 2013, Lemma 2.2.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
open scoped BigOperators

theorem two_point_hoeffding_mgf_bound (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a + (1 - p) * b + (a - b) ^ 2 / 8) := by sorry
