-- Prove2me | Theorems.Thm_weighted_sum_chebyshev_lower_tail_bound
-- name    : weighted_sum_chebyshev_lower_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-03T22:41:54.699519+00:00
-- url     : https://prove2.me/theorems/c147ebb6-a1ad-40f3-a07a-d0cb0f08f3dd
-- statement:
--   Chebyshev lower tail for a weighted sum of i.i.d. centered unit-variance noise: if $E[Z]=0$ and $E[Z^2]=1$, then for any weights $a_i$ and any $c>0$, $P[\sum_i a_iZ_i\ge -c]\ge 1-(\sum_i a_i^2)/c^2$, since $\mathrm{Var}(\sum_i a_iZ_i)=\sum_i a_i^2$ by independence.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, App. C.2 (proof of Lemma 4.5)

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory

theorem weighted_sum_chebyshev_lower_tail_bound
    (N : ℕ) (noise : Measure ℝ) [IsProbabilityMeasure noise]
    (a : Fin N → ℝ) (c : ℝ)
    (hmean : ∫ z, z ∂noise = 0) (hvar : ∫ z, z ^ 2 ∂noise = 1)
    (hc : 0 < c) :
    1 - (∑ i, a i ^ 2) / c ^ 2 ≤
      (Measure.pi fun _ : Fin N => noise).real {z | -c ≤ ∑ i, a i * z i} := by sorry
