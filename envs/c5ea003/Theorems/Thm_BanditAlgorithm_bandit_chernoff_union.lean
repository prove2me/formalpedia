-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_chernoff_union
-- name    : BanditAlgorithm.bandit_chernoff_union
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:29:41.787138+00:00
-- url     : https://prove2.me/theorems/90299fda-6d1e-4a06-a8ca-f2e896d42298
-- title:
--   Weighted-union Chernoff bound over a family of tilts (discrete method of mixtures)
-- statement:
--   The weighted-union Chernoff bound over a countable family of tilts (the discrete method of mixtures). Let $(\lambda_j)_{j\in\mathbb N}$ be arbitrary tilts and $(w_j)_{j\in\mathbb N}$ positive weights with $\sum_j w_j\le1$. Then for every $x$,
--   $$\mathbb P\left(\exists j:\ \lambda_j\bigl(S_a(n)-T_a(n)\mu_a\bigr)-\frac{\lambda_j^2}{2}T_a(n)\ \ge\ x+\log\frac{1}{w_j}\right)\ \le\ e^{-x}.$$
--
--   A fixed-tilt bound is useless when the optimal tilt depends on the realised pull count, which is random; this upgrades it to hold simultaneously over a whole family, at the price of $\log(1/w_j)$ for the $j$-th member. It is the discrete counterpart of integrating the exponential martingale against a prior on $\lambda$, and needs nothing beyond a union bound. Taking $w_j=2^{-(j+1)}$ and the $\lambda_j$ on a geometric grid is the standard concrete instance.
-- source:
--   The discrete method of mixtures (weighted union over a countable family of tilts); standard, see Garivier & Kaufmann, COLT 2016, Section 4, and Magureanu, Combes & Proutiere, COLT 2014.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_chernoff_union {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (n : ℕ)
    (lams : ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (hle : ∑' j, w j ≤ 1) (x : ℝ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ j : ℕ,
          x + Real.log (1 / w j)
            ≤ lams j * ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
                - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a)
              - lams j ^ 2 * (BanditAlgorithm.trajPullCount a n ω : ℝ) / 2}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  sorry
