-- Prove2me | Theorems.Thm_BanditAlgorithm_lintegral_enat_eq_tsum_measure_lt
-- name    : BanditAlgorithm.lintegral_enat_eq_tsum_measure_lt
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:30:47.748389+00:00
-- url     : https://prove2.me/theorems/864d1b88-dfae-4209-9949-7534fbee4e75
-- title:
--   Tail-sum formula for the expectation of an ℕ∞-valued random variable
-- statement:
--   For an $\mathbb N\cup\{\infty\}$-valued measurable $\tau$ on a measure space $(\Omega,\mu)$, the tail-sum formula holds in $[0,\infty]$:
--   $$\int_\Omega \tau\,d\mu=\sum_{n=0}^{\infty}\mu\bigl(\{\tau>n\}\bigr).$$
--
--   Mathlib has this for $\mathbb N$-valued and for $\mathbb R_{\ge0}$-valued random variables, but not for $\mathbb N\cup\{\infty\}$-valued ones, which is the type of a bandit stopping time (Definition 33.4 explicitly allows $\tau=\infty$). It is the tool that converts a family of round-by-round deviation bounds $\mathbb P(\tau>n)\le\varepsilon_n$ into a bound on $\mathbb E[\tau]$, which is exactly how the sample-complexity half of Theorem 33.6 is proved.
-- source:
--   Standard layer-cake / Fubini-Tonelli argument; used in this form in Garivier & Kaufmann, COLT 2016, Proposition 13, and Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 33.2.2.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory ENNReal

theorem BanditAlgorithm.lintegral_enat_eq_tsum_measure_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {τ : Ω → ℕ∞} (hτ : Measurable τ) :
    ∫⁻ ω, (τ ω : ENNReal) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < τ ω} := by
  sorry
