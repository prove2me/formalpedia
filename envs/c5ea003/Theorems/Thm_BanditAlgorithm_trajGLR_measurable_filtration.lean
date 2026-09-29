-- Prove2me | Theorems.Thm_BanditAlgorithm_trajGLR_measurable_filtration
-- name    : BanditAlgorithm.trajGLR_measurable_filtration
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:09:28.760205+00:00
-- url     : https://prove2.me/theorems/ce72ade8-6b02-42cc-b749-027d5197c752
-- title:
--   The GLR statistic Z_t is adapted to the natural filtration
-- statement:
--   The generalised-likelihood-ratio statistic
--   $$Z_t=\min_{j\neq \hat\imath(t)}\ \frac{1}{2}\,\frac{T_{\hat\imath(t)}(t)\,T_j(t)}{T_{\hat\imath(t)}(t)+T_j(t)}\bigl(\hat\mu_{\hat\imath(t)}(t)-\hat\mu_j(t)\bigr)^2$$
--   of Lattimore--Szepesv\'ari p.\ 409 is $\mathcal F_t$-measurable, where $\mathcal F_t=\sigma(A_1,X_1,\dots,A_t,X_t)$ is the natural filtration.
--
--   This is what makes $\tau_\delta=\min\{t: Z_t\ge\beta_t(\delta)\}$ a stopping time, and it is not immediate: $Z_t$ is defined through the empirical best arm $\hat\imath(t)$, which is a `Classical.choose` maximiser and carries no measurability of its own. The point is that $Z_t$ is tie-independent -- if two arms are tied for the empirical best, the pair term between them vanishes, so $Z_t=0$ regardless of which is selected -- and therefore agrees with the value computed at the canonical least-index maximiser, which is $\mathcal F_t$-measurable.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 33.2.2, Algorithm 21 and p. 409.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.trajGLR_measurable_filtration {k : ℕ} [NeZero k] (t : ℕ) :
    Measurable[BanditAlgorithm.banditFiltration k t] (BanditAlgorithm.trajGLR (k := k) t) := by
  sorry
