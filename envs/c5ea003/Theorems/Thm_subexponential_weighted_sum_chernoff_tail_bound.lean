-- Prove2me | Theorems.Thm_subexponential_weighted_sum_chernoff_tail_bound
-- name    : subexponential_weighted_sum_chernoff_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-03T22:41:47.504663+00:00
-- url     : https://prove2.me/theorems/ce0ccd05-f4f7-4660-b9a0-3cecaa6d523d
-- statement:
--   Chernoff bound for the upper tail of a weighted sum of i.i.d. sub-exponential noise. Let $Z_1,\dots,Z_N$ be i.i.d. with $E[e^{\lambda Z}]\le e^{\lambda^2\gamma^2/2}$ for all $|\lambda|<1/\xi$ (the MGF hypothesis stated as a lower Lebesgue integral, so it also asserts finiteness), and let $|a_i|\le 1$. Then for every Chernoff parameter $t\in(0,1/\xi)$ and every threshold $s$, $P[\sum_i a_iZ_i\ge s]\le\exp(-ts+t^2(\sum_i a_i^2)\gamma^2/2)$. Cf. Vershynin, High-Dimensional Probability, Prop. 2.7.1; the regime optimization over $t$ is left to consumers.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, App. C.2 (proof of Lemma 4.5)

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic

open MeasureTheory

theorem subexponential_weighted_sum_chernoff_tail_bound
    (N : ℕ) (noise : Measure ℝ) [IsProbabilityMeasure noise]
    (γ ξ : ℝ) (a : Fin N → ℝ) (t s : ℝ)
    (hξ : 0 < ξ) (ha : ∀ i, |a i| ≤ 1)
    (hse : ∀ l : ℝ, |l| < 1 / ξ →
      ∫⁻ z, ENNReal.ofReal (Real.exp (l * z)) ∂noise ≤
        ENNReal.ofReal (Real.exp (l ^ 2 * γ ^ 2 / 2)))
    (ht : 0 < t) (htξ : t < 1 / ξ) :
    (Measure.pi fun _ : Fin N => noise).real {z | s ≤ ∑ i, a i * z i} ≤
      Real.exp (-t * s + t ^ 2 * (∑ i, a i ^ 2) * γ ^ 2 / 2) := by sorry
