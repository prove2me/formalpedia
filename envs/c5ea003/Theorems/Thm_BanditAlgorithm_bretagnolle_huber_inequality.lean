-- Prove2me | Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
-- name    : BanditAlgorithm.bretagnolle_huber_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-18T23:57:34.010761+00:00
-- url     : https://prove2.me/theorems/d5e10404-0a7b-48d7-9426-b781d5b193bb
-- statement:
--   (Bretagnolle–Huber, GOAL) Let $P$ and $Q$ be probability measures on the same measurable space $(\Omega, \mathcal{F})$ with $D(P,Q) = $ `klDiv P Q` finite, and let $A \in \mathcal{F}$ be measurable. Then
--
--   $$P(A) + Q(A^c) \ge \frac{1}{2}\exp(-D(P,Q)),$$
--
--   with probabilities as `Measure.real`. CRITICAL BOUNDARY: the hypothesis $D(P,Q) \ne \infty$ is REQUIRED — without it the Lean statement is FALSE, since `(∞).toReal = 0` would make the right-hand side $\frac12$ while e.g. $P = \delta_0$, $Q = \delta_1$, $A = \{1\}$ gives $P(A)+Q(A^c) = 0$. The book's statement is trivially true at $D = \infty$ (right-hand side $\frac12 e^{-\infty} = 0$); only the `toReal` junk-value encoding breaks.
-- source:
--   L&S Theorem 14.2, Eq. (14.7), p.190

import Mathlib.InformationTheory.KullbackLeibler.Basic


open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem BanditAlgorithm.bretagnolle_huber_inequality {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  sorry
