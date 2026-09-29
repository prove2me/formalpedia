-- Prove2me | Theorems.Thm_BanditAlgorithm_summable_sq_mul_exp_neg_sqrt
-- name    : BanditAlgorithm.summable_sq_mul_exp_neg_sqrt
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T15:45:54.656357+00:00
-- url     : https://prove2.me/theorems/84108760-b9a6-45fe-bc1a-d974b3aae4e7
-- title:
--   $\sum_m (m+1)^2 e^{-c\sqrt m}<\infty$
-- statement:
--   For every $c>0$,
--   $$\sum_{m\ge 0}(m+1)^2 e^{-c\sqrt m}<\infty .$$
--
--   A sub-exponential decay absorbs any polynomial weight. The quadratic weight is the one a *delayed* covering argument costs: if a failure at round $n$ is covered by failures at rounds $m\ge\theta n$, exchanging the two sums replaces the weight $(n+1)$ by $\sum_{n:\theta n\le m}(n+1)\asymp(m+1)^2$, so a first moment on one side is a second moment on the other.
--
--   The comparison is $\log x\le 4x^{1/4}$, obtained by applying $\log\le 2\sqrt{\cdot}$ at $\sqrt x$ rather than at $x$. It gives $4\log x\le 16x^{1/4}\le c\sqrt x$ once $x\ge(16/c)^4$, hence $e^{-c\sqrt x}\le x^{-4}$, and a fourth power leaves a convergent $\sum(m+1)^{-2}$ against the quadratic weight.
-- source:
--   Tail estimate behind Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6; used for the settling time of Garivier & Kaufmann, COLT 2016, Proposition 13.

import Definitions.Def_TrackAndStop
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Topology

theorem BanditAlgorithm.summable_sq_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ 2 * Real.exp (-(c * Real.sqrt (m : ℝ))) := by
  sorry
