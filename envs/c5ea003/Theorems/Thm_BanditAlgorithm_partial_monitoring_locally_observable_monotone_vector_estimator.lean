-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_monotone_vector_estimator
-- name    : BanditAlgorithm.partial_monitoring_locally_observable_monotone_vector_estimator
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:15:15.240074+00:00
-- url     : https://prove2.me/theorems/0f6f93e7-0b0b-4177-82e3-e8bc87061e25
-- title:
--   Monotone path-summed estimator for locally observable games
-- statement:
--   In a locally observable finite partial-monitoring game, choose a Pareto-cell cover $S$. There is a finite constant $V\ge0$ such that, for every mixed outcome $\lambda$, local estimators can be summed along the loss-monotone neighbour paths to form a vector estimator $f$. It is uniformly bounded by $V$, and whenever $f(a,\sigma)_b\ne0$, action $a$ has no larger $\lambda$-expected loss than comparator $b$.\n\nThe estimator telescopes along each path to estimate $L_b-L_{\mathrm{root}}$. Lemma 37.8 shows that every revealing action in an edge neighbourhood has loss between the two endpoint losses, which gives the monotone-support property.\n\n**Formalization Note** A crude finite sum of all selected edge-estimator norms supplies $V$; only existence of a game-dependent constant is needed downstream.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), §37.7, proof of Theorem 37.17, printed pp. 501–502, using Lemmas 37.8 and 37.21. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_locally_observable_monotone_vector_estimator
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ V : ℝ,
      S.Nonempty ∧ 0 ≤ V ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ f : Fin k → 𝕊 → Fin k → ℝ,
          PMVectorEstimatorOn G S f ∧
          (∀ a σ b, |f a σ b| ≤ V) ∧
          ∀ a σ b, f a σ b ≠ 0 →
            ∑ i : Fin d, G.L a i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i := by sorry
