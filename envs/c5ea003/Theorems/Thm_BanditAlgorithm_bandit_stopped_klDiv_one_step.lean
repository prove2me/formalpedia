-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_stopped_klDiv_one_step
-- name    : BanditAlgorithm.bandit_stopped_klDiv_one_step
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T20:32:38.413002+00:00
-- url     : https://prove2.me/theorems/4ea01600-bb2d-4c0c-9d89-ded852f95c99
-- title:
--   One-step KL increment for a stopped bandit experiment
-- statement:
--   Run the same adaptive $k$-armed bandit policy $\pi$ in two environments $\nu=(P_i)_{i=1}^k$ and $\nu^{\prime}=(P_i^{\prime})_{i=1}^k$, and let $\tau$ be a stopping time. Let $P^{\pi}_{\nu,\tau\wedge n}$ and $P^{\pi}_{\nu^{\prime},\tau\wedge n}$ denote the two trajectory laws restricted to the sigma-algebra observed by time $\tau\wedge n$. Then, for every $n\ge 0$,
--
--   $$
--   D\!\left(P^{\pi}_{\nu,\tau\wedge(n+1)}\,\middle\Vert\,P^{\pi}_{\nu^{\prime},\tau\wedge(n+1)}\right)
--   \le
--   D\!\left(P^{\pi}_{\nu,\tau\wedge n}\,\middle\Vert\,P^{\pi}_{\nu^{\prime},\tau\wedge n}\right)
--   +
--   \sum_{i=1}^{k}
--   \mathbb P_{\nu,\pi}(n<\tau,\ A_{n+1}=i)\,D(P_i\Vert P_i^{\prime}).
--   $$
--
--   This is the one-round chain-rule increment for a stopped adaptive experiment. Iterating it yields the expected-information bound at a bounded stopping time, and the extended-nonnegative-real formulation also covers singular arm laws.
--
--   **Formalization Note** Rounds are zero-indexed, so the coordinate $\omega_n$ represents $(A_{n+1},X_{n+1})$. The stopped laws are represented by trimming the infinite trajectory measures to Mathlib’s stopped measurable spaces.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211: stopped likelihood-ratio chain rule and truncation argument extending Lemma 15.1; compare Lemma 15.1, Eqs. (15.1)–(15.2), printed pp. 198–199.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_stopped_klDiv_one_step
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const (n + 1)).measurableSpace
        ((banditTrajMeasure ν π).trim
          (hτ.min_const (n + 1)).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim
          (hτ.min_const (n + 1)).measurableSpace_le) ≤
      @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
          ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) +
        ∑ i, (banditTrajMeasure ν π)
            {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
          klDiv (ν.P i) (ν'.P i) := by
  sorry
