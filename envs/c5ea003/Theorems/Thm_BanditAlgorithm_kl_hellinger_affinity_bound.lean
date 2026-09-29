-- Prove2me | Theorems.Thm_BanditAlgorithm_kl_hellinger_affinity_bound
-- name    : BanditAlgorithm.kl_hellinger_affinity_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-19T01:47:16.71765+00:00
-- url     : https://prove2.me/theorems/72d4bba1-675d-4d5a-9c1b-d366c8026e06
-- title:
--   Hellinger affinity vs. KL: $e^{-D(P,Q)}\le\big(\int\sqrt{pq}\big)^2$
-- statement:
--   For probability measures P and Q with finite relative entropy, their squared Hellinger affinity is bounded below by the exponential of minus the KL divergence: $\exp(-D(P,Q))\le(\int\sqrt{pq}\,dν)^2$, where ν=P+Q. The finite-divergence hypothesis is required because ENNReal.toReal uses a junk value at infinity.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 14.2, Jensen/KL display immediately after Eq. (14.9), printed p. 191 / PDF p. 200.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.kl_hellinger_affinity_bound {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (Real.exp (-(klDiv P Q).toReal)) ≤
      (∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ (2⁻¹ : ℝ)
        ∂(P + Q)) ^ 2 := by sorry
