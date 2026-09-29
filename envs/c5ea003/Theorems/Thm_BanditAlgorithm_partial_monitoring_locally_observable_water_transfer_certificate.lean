-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_water_transfer_certificate
-- name    : BanditAlgorithm.partial_monitoring_locally_observable_water_transfer_certificate
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:42:10.625361+00:00
-- url     : https://prove2.me/theorems/00f97a52-9bac-4147-b145-879e6aecda2c
-- title:
--   Water-transfer certificate for locally observable partial monitoring
-- statement:
--   Let G be a locally observable finite partial-monitoring game with losses in [0,1]. There are a nonempty comparator set S, a nonnegative constant K, and eta_0>0 such that S always contains a hindsight-optimal comparator. For every 0<eta<=eta_0 and every distribution q supported on S, there are an interior sampling distribution p and vector estimator f with three simultaneous properties: the exploration loss is at most eta K for every outcome; every importance-weighted coordinate eta f/p is at least -1; and its q-weighted conditional second moment is at most eta^2 K for every outcome.
--
--   In formulas, the certificate gives
--
--   $$
--   \sum_a(p_a-q_a)L_{a i}\leq\eta K,\qquad \frac{\eta f(a,\sigma)_b}{p_a}\geq-1,
--   $$
--
--   and
--
--   $$
--   \sum_a p_a\sum_b q_b\left(\frac{\eta f(a,\Phi_{a i})_b}{p_a}\right)^2\leq\eta^2K.
--   $$
--
--   This packages exactly the geometric water-transfer, in-tree, local-estimator, and minimax output used immediately before the quadratic stability inequality in the proof of Theorem 37.17.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Lemmas 37.20--37.21 and proof of Theorem 37.17, printed pp. 500--502, especially equations (37.16)--(37.17), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

/-! Lattimore--Szepesvári, Theorem 37.17 and Lemmas 37.20--37.21,
printed pp. 500--502: the water-transfer certificate used before applying
the quadratic stability bound (37.15). -/

theorem partial_monitoring_locally_observable_water_transfer_certificate
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ K η₀ : ℝ,
      S.Nonempty ∧ 0 ≤ K ∧ 0 < η₀ ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ q : Fin k → ℝ, PMSupportedOn S q →
          ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
            PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
            (∀ i : Fin d,
              ∑ a : Fin k, (p a - q a) * G.L a i ≤ η * K) ∧
            (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
            ∀ i : Fin d,
              ∑ a : Fin k, p a *
                (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
                  η ^ 2 * K := by
  sorry

end BanditAlgorithm
