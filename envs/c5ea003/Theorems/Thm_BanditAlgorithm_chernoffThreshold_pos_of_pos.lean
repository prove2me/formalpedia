-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoffThreshold_pos_of_pos
-- name    : BanditAlgorithm.chernoffThreshold_pos_of_pos
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:09:51.76055+00:00
-- url     : https://prove2.me/theorems/302cd17d-8dc4-408d-a9fa-62f1baba2d1a
-- title:
--   Chernoff's threshold is strictly positive
-- statement:
--   For $k\ge 1$ and $\delta>0$ the threshold of Lattimore--Szepesv\'ari Lemma 33.7,
--   $$\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta),$$
--   is strictly positive at every round $t$, where $f(x)=e^{k-x}(x/k)^k$ and $f^{-1}(\delta)$ is the least $x\ge k$ with $f(x)\le\delta$.
--
--   Positivity is used twice in the analysis of Chernoff's stopping rule: it forces $Z_{\tau}>0$ at the stopping time, hence a *unique* empirical best arm there (so the recommendation is well defined and measurable), and it makes the threshold usable as the $\beta$ of the self-normalised deviation bound.
-- source:
--   Elementary property of the threshold beta_t(delta) = k log(t^2+t) + f^{-1}(delta) introduced in Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. Positivity is not stated there; it is needed here to make Chernoff's recommendation well defined.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoffThreshold_pos_of_pos {k : ℕ} (hk : 0 < k) {δ : ℝ}
    (hδ : 0 < δ) (t : ℕ) :
    0 < BanditAlgorithm.chernoffThreshold k δ t := by
  sorry
