-- Prove2me | Theorems.Thm_BanditAlgorithm_expWeights_psi_regret
-- name    : BanditAlgorithm.expWeights_psi_regret
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T20:15:57.782533+00:00
-- url     : https://prove2.me/theorems/763272b6-c54b-4a91-8cb0-03b986d6a196
-- title:
--   Exponential-weights regret with the exact $\Psi_q$ stability term
-- statement:
--   Let $k\ge1$, let $\eta>0$, and let $\widehat y_t\in\mathbb R^k$ be an arbitrary sequence. Define exponential-weights normalizers and distributions by
--
--   $$
--   W_t=\sum_{a=1}^k\exp\!\left(-\eta\sum_{s<t}\widehat y_{sa}\right),
--   \qquad
--   Q_{ta}=\frac{\exp\!\left(-\eta\sum_{s<t}\widehat y_{sa}\right)}{W_t}.
--   $$
--
--   Then for every comparator action $a_0$,
--
--   $$
--   \sum_{t=0}^{n-1}\sum_{a=1}^k Q_{ta}(\widehat y_{ta}-\widehat y_{ta_0})
--   \le \frac{\log k}{\eta}
--    +\frac1\eta\sum_{t=0}^{n-1}\Psi_{Q_t}(\eta\widehat y_t),
--   $$
--
--   where
--
--   $$
--   \Psi_q(z)=\sum_a q_a\bigl(e^{-z_a}+z_a-1\bigr).
--   $$
--
--   No boundedness or sign condition is imposed on the estimated-loss vectors. This is the deterministic exponential-weights inequality used by Algorithm 26 before taking expectations.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), equation (37.11), printed p. 493, used in the proof of Theorem 37.15 on pp. 494–495, https://tor-lattimore.com/downloads/book/book.pdf

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Order

open scoped BigOperators

namespace BanditAlgorithm

theorem expWeights_psi_regret
    (k n : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (y : ℕ → Fin k → ℝ) :
    let W := fun t : ℕ =>
      ∑ a : Fin k, Real.exp (- (η * ∑ s ∈ Finset.range t, y s a))
    let Q := fun t : ℕ => fun a : Fin k =>
      Real.exp (- (η * ∑ s ∈ Finset.range t, y s a)) / W t
    ∀ a₀ : Fin k,
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * (y t a - y t a₀)) ≤
        Real.log k / η + (1 / η) *
          ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by sorry
