-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_algorithm26_solver
-- name    : BanditAlgorithm.partial_monitoring_locally_observable_algorithm26_solver
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:33:37.033568+00:00
-- url     : https://prove2.me/theorems/6d06f158-590f-4572-8dbf-2d31ecdae501
-- title:
--   Locally observable Algorithm 26 optimizer and tuning bound
-- statement:
--   Let G be a locally observable finite partial-monitoring game with at least two actions, at least one outcome, and losses in [0,1]. Then there are a nonempty comparator set S and a constant C>0 such that S contains a hindsight-optimal comparator for every outcome sequence. Moreover, for every positive horizon n one can tune a learning rate eta>0 and a nonnegative one-step bound B so that
--
--   $$
--   \frac{\log |S|}{\eta}+n\eta B \leq C\,\max\{1,v_{\mathrm{loc}}\}\,k^{3/2}\sqrt{n\log k},
--   $$
--
--   and, for every distribution q supported on S, choose an interior sampling distribution p and vector estimator f whose Algorithm 26 exploration--stability objective is at most B for every outcome.
--
--   This isolates the finite-dimensional geometric optimization and tuning content of the locally observable upper bound. The stochastic policy construction and potential argument are deliberately excluded and supplied by the separate Algorithm 26 master theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.17 and Sections 37.7--37.7.1, printed pp. 498--502; combined with Theorem 37.15 tuning on pp. 494--496, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

/-! Qualitative form of Lattimore--Szepesvári, Theorem 37.17, printed
pp. 498--502, packaged for the Algorithm 26 master bound. -/

theorem partial_monitoring_locally_observable_algorithm26_solver
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ C : ℝ, S.Nonempty ∧ 0 < C ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ n : ℕ, 0 < n → ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧
        Real.log S.card / η + (n : ℝ) * η * B ≤
          C * max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt (n * Real.log k) ∧
          ∀ q : Fin k → ℝ, PMSupportedOn S q →
            ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
              PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
              ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ B := by
  sorry

end BanditAlgorithm
