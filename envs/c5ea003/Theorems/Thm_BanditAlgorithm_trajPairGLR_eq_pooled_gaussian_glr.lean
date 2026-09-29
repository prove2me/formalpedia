-- Prove2me | Theorems.Thm_BanditAlgorithm_trajPairGLR_eq_pooled_gaussian_glr
-- name    : BanditAlgorithm.trajPairGLR_eq_pooled_gaussian_glr
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:21:53.399995+00:00
-- url     : https://prove2.me/theorems/3e97dea9-7aab-4b0b-b9ec-930e1ca226c4
-- title:
--   The pair statistic of Track-and-Stop is the Gaussian pairwise GLR
-- statement:
--   For a pair of arms $a\ne b$ with $T_a(t)+T_b(t)>0$, the pairwise Gaussian generalised likelihood ratio admits the pooled-mean closed form
--   $$\frac{1}{2}\cdot\frac{T_a(t)T_b(t)}{T_a(t)+T_b(t)}\bigl(\hat\mu_a(t)-\hat\mu_b(t)\bigr)^2=\inf_{m\in\mathbb R}\left\{\frac{T_a(t)}{2}\bigl(\hat\mu_a(t)-m\bigr)^2+\frac{T_b(t)}{2}\bigl(\hat\mu_b(t)-m\bigr)^2\right\}.$$
--
--   The right-hand side is the definition of the GLR statistic -- the cheapest way, in KL divergence, to make arms $a$ and $b$ share a common mean -- and the left-hand side is the closed form that Lattimore--Szepesv\'ari manipulate on p.\ 409. The identity is the exact decomposition
--   $$p(u-m)^2+q(v-m)^2=(p+q)(m-m^*)^2+\frac{pq}{p+q}(u-v)^2,\qquad m^*=\frac{pu+qv}{p+q},$$
--   so the infimum is attained at the pooled mean $m^*$. It is the single most-used algebraic fact in this development.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 33.2.2, p. 409; Garivier & Kaufmann, COLT 2016, Section 3.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

theorem BanditAlgorithm.trajPairGLR_eq_pooled_gaussian_glr {k : ℕ} (a b : Fin k) (t : ℕ)
    (ω : ℕ → Fin k × ℝ)
    (h : 0 < (BanditAlgorithm.trajPullCount a t ω : ℝ)
      + (BanditAlgorithm.trajPullCount b t ω : ℝ)) :
    BanditAlgorithm.trajPairGLR a b t ω
      = ⨅ m : ℝ, ((BanditAlgorithm.trajPullCount a t ω : ℝ)
            * ((BanditAlgorithm.trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (BanditAlgorithm.trajPullCount b t ω : ℝ)
            * ((BanditAlgorithm.trajEmpiricalMean b t ω - m) ^ 2 / 2)) := by
  sorry
