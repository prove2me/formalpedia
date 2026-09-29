-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStochMeasure_kl_toReal_le_expected_outside_count
-- name    : BanditAlgorithm.pmStochMeasure_kl_toReal_le_expected_outside_count
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T19:26:06.959312+00:00
-- url     : https://prove2.me/theorems/0afbb1b1-7dfa-4117-9514-20f4b3e3659d
-- title:
--   Adaptive history KL is bounded by expected outside-action count
-- statement:
--   Consider two stochastic partial-monitoring environments $u$ and $v$ used with the same adaptive policy $\pi$. Let $N$ be a set of actions whose feedback laws agree under the two environments. Suppose every action outside $N$ has one-round Kullback–Leibler divergence at most a finite constant $B$, and all one-round divergences are finite. If $\widetilde T_N(n)$ denotes the number of rounds up to time $n$ on which the learner selects an action outside $N$, then
--
--   $$
--   D(P_u^n\|P_v^n)
--   \le
--   B\,\mathbb E_u[\widetilde T_N(n)].
--   $$
--
--   Here $P_u^n$ and $P_v^n$ are the complete feedback-history laws induced by $u$ and $v$. This is the real-valued expected-count form of the adaptive KL chain rule used in information-theoretic lower bounds for partial monitoring.
--
--   **Formalization Note** The platform chain-rule theorem is naturally stated in extended nonnegative reals. This theorem records the finiteness argument and converts its predictable selection-mass bound into the expected count on complete histories.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 37.12 proof, printed p. 490, Eqs. (37.8)–(37.9), with the outside-neighbourhood count defined on printed p. 491.

import Theorems.Thm_BanditAlgorithm_pmStochMeasure_kl_le_outside_selection
import Theorems.Thm_BanditAlgorithm_pmStoch_expected_actionSetCount_eq_selection_mass

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStochMeasure_kl_toReal_le_expected_outside_count
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d)) (N : Finset (Fin k)) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (heq : ∀ c, c ∈ N → pmSignalMeasure G u c = pmSignalMeasure G v c)
    (hle : ∀ c, c ∉ N → klDiv (pmSignalMeasure G u c)
      (pmSignalMeasure G v c) ≤ B) : ∀ n : ℕ,
    (klDiv (pmStochMeasure G π u hu n)
      (pmStochMeasure G π v hv n)).toReal ≤
      B.toReal *
        ∫ h, ∑ t : Fin n,
          (if (h t).1 ∉ N then (1 : ℝ) else 0)
          ∂pmStochMeasure G π u hu n := by
  sorry
