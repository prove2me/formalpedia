-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_one_step_information_ratio_varying_reference
-- name    : BanditAlgorithm.thompson_sampling_one_step_information_ratio_varying_reference
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:40:04.510058+00:00
-- url     : https://prove2.me/theorems/5e717e38-69d7-474c-b010-f201b24e1aa1
-- title:
--   One-step information-ratio bound with arm-dependent reference laws
-- statement:
--   Let $p_a$ be real weights. For every arm $a\in[k]$, let $P_a$ and $M_a$ be probability measures on the same measurable space, and let $r_a$ be a measurable function taking values in $[0,1]$. If every $D(P_a\|M_a)$ is finite, then
--
--   $$
--   \left(\sum_{a=1}^k p_a\bigl(\mathbb E_{P_a}r_a-\mathbb E_{M_a}r_a\bigr)\right)^2
--   \le
--   \frac{k}{2}\sum_{a=1}^k p_a^2D(P_a\|M_a).
--   $$
--
--   This is the analytic Pinsker–Cauchy–Schwarz step in the one-round Thompson-sampling information-ratio argument, allowing the reference distribution to depend on the arm.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; Pinsker and Cauchy–Schwarz steps.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

theorem thompson_sampling_one_step_information_ratio_varying_reference
    {k : ℕ} {Omega : Type} {mOmega : MeasurableSpace Omega}
    (p : Fin k → ℝ) (P M : Fin k → Measure Omega)
    [∀ a, IsProbabilityMeasure (P a)] [∀ a, IsProbabilityMeasure (M a)]
    (reward : Fin k → Omega → ℝ)
    (hreward : ∀ a, Measurable (reward a))
    (hreward0 : ∀ a x, 0 ≤ reward a x)
    (hreward1 : ∀ a x, reward a x ≤ 1)
    (hfinite : ∀ a, klDiv (P a) (M a) ≠ ∞) :
    (∑ a, p a * ((∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂(M a))) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal := by
  sorry

end BanditAlgorithm
