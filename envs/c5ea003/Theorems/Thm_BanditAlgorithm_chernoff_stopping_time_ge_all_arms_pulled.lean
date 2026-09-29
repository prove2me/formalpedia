-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_stopping_time_ge_all_arms_pulled
-- name    : BanditAlgorithm.chernoff_stopping_time_ge_all_arms_pulled
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:17:57.194013+00:00
-- url     : https://prove2.me/theorems/d5296eae-d3e2-4a03-8d11-3526534b0722
-- title:
--   Chernoff's stopping time is at least the time all arms are pulled
-- statement:
--   For $k\ge2$ arms, every $\delta>0$ and every trajectory $\omega$,
--   $$\inf\{n:\ T_i(n)>0\text{ for every arm }i\}\ \le\ \tau_\delta(\omega),$$
--   where $\tau_\delta$ is Chernoff's stopping time and $T_i(n)$ is the number of pulls of arm $i$ in the first $n$ rounds.
--
--   The reason is that the generalised-likelihood-ratio statistic
--   $$Z_t=\min_{j\ne\hat\imath(t)}\tfrac12\cdot\frac{T_{\hat\imath}T_j}{T_{\hat\imath}+T_j}\,(\hat\mu_{\hat\imath}-\hat\mu_j)^2$$
--   carries the factor $T_{\hat\imath}T_j/(T_{\hat\imath}+T_j)$, which vanishes as soon as *either* count is zero. If some arm is unplayed at round $t$ then $Z_t=0$: either that arm is one of the competitors $j$ and its own term vanishes, or it is the empirical maximiser and then every term vanishes. The threshold $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ is strictly positive, so the rule cannot fire.
--
--   The consequence is a constraint on any bound of the form $\tau_\delta\le W$ with $W$ integrable and independent of $\delta$: such a bound forces the expected time to play every arm to be finite, a quantitative property of the *sampling rule*. Almost-sure convergence of the empirical allocation does not supply it — a rule may postpone the first pull of arm $2$ to a round $M$ that is finite almost surely but has $\mathbb E[M]=\infty$, and still satisfy $T_i(t)/t\to\alpha_i$ almost surely, since a finite delay does not affect a Cesaro limit. This is why the analysis of Track-and-Stop needs forced exploration and not merely tracking.
-- source:
--   Elementary consequence of the closed form of the GLR statistic in Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), p. 409; it is the obstruction that makes the forced exploration of Garivier & Kaufmann's D-Tracking (COLT 2016, Lemma 7) necessary rather than merely convenient.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal Filter Topology

theorem BanditAlgorithm.chernoff_stopping_time_ge_all_arms_pulled {k : ℕ} [NeZero k]
    (hk2 : 1 < k) {δ : ℝ} (hδ : 0 < δ) (ω : ℕ → Fin k × ℝ) :
    ((sInf {n : ℕ | ∀ i : Fin k, 0 < BanditAlgorithm.trajPullCount i n ω} : ℕ) : ℕ∞)
      ≤ BanditAlgorithm.chernoffStoppingTime (k := k) δ ω := by
  sorry
