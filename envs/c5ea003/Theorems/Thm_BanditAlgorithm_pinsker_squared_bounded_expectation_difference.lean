-- Prove2me | Theorems.Thm_BanditAlgorithm_pinsker_squared_bounded_expectation_difference
-- name    : BanditAlgorithm.pinsker_squared_bounded_expectation_difference
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:31:07.707737+00:00
-- url     : https://prove2.me/theorems/e46963d4-8316-4597-afbb-841b5af12ce0
-- title:
--   Pinsker inequality for bounded expectations
-- statement:
--   Let $P$ and $Q$ be probability measures and let $f$ be a measurable function with values in $[0,1]$. If $D(P\,\|\,Q)$ is finite, then
--
--   $$
--   2\left(\mathbb E_Q[f]-\mathbb E_P[f]\right)^2 \le D(P\,\|\,Q).
--   $$
--
--   This is the bounded-expectation form of Pinsker’s inequality used in the one-step Thompson-sampling information-ratio argument.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 470 (PDF p. 479), proof of Lemma 36.7, first inequality after the definition of Δ_t; the extension from events to [0,1]-valued rewards is the standard layer-cake form of Pinsker.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.pinsker_squared_bounded_expectation_difference
    {Omega : Type} {mOmega : MeasurableSpace Omega}
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Omega → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hD : klDiv P Q ≠ ∞) :
    2 * ((∫ x, f x ∂Q) - ∫ x, f x ∂P) ^ 2 ≤ (klDiv P Q).toReal := by
  sorry
