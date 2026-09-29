-- Prove2me | Theorems.Thm_BanditAlgorithm_finite_information_ratio_cauchy_schwarz
-- name    : BanditAlgorithm.finite_information_ratio_cauchy_schwarz
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:35:48.463098+00:00
-- url     : https://prove2.me/theorems/47389f5c-eea3-4323-9be4-33a02227c375
-- title:
--   Finite-action Cauchy–Schwarz information-ratio step
-- statement:
--   For real vectors $p$, $g$, and $I$ indexed by $k$ actions, suppose each coordinate satisfies $2g_a^2\le I_a$. Then
--
--   $$
--   \left(\sum_a p_a g_a\right)^2 \le \frac{k}{2}\sum_a p_a^2 I_a.
--   $$
--
--   This is the finite-dimensional Cauchy–Schwarz step used in the Thompson-sampling information-ratio bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 470 (PDF p. 479), proof of Lemma 36.7, the Cauchy–Schwarz inequality immediately before the final Bayes-rule equality.

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem BanditAlgorithm.finite_information_ratio_cauchy_schwarz {k : ℕ}
    (p gap info : Fin k → ℝ)
    (hpoint : ∀ a, 2 * gap a ^ 2 ≤ info a) :
    (∑ a, p a * gap a) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * info a := by
  sorry
