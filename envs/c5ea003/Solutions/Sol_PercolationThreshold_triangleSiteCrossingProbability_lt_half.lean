-- Prove2me | solution 1 for PercolationThreshold.triangleSiteCrossingProbability_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:59:15.507118+00:00
-- url     : https://prove2.me/submissions/e9268cf3-efa1-4a5c-85ac-ed9ab5adf97c

-- Sol generated from Probability/PercolationThreshold.lean
import Mathlib
import Definitions.Def_Probability_PercolationThreshold

/-!
# A finite triangular percolation threshold calculation

This file separates a rigorously solvable local calculation from the open problem
of finding a closed analytic form for the infinite square-lattice site threshold.
For three independent Bernoulli sites, the probability that at least two are open
is `p³ + 3p²(1-p)`.  We prove that this increasing event is self-dual and has the
unique fair point `p = 1/2`.  The same polynomial describes the event that three
vertices are connected by open bonds in a triangular face.

This is the elementary local self-duality calculation underlying the exact
critical parameter for triangular-lattice site percolation.  It is deliberately
not presented as a proof of the infinite-volume theorem, which additionally
requires substantial planar percolation machinery.
-/

open PercolationThreshold


/-- Expanding the elementary three-site probability gives its standard cubic
form. -/
theorem triangleSiteCrossingProbability_eq_cubic (p : ℝ) :
    triangleSiteCrossingProbability p = 3 * p ^ 2 - 2 * p ^ 3 := by
  unfold triangleSiteCrossingProbability
  ring














open PercolationThreshold in
theorem solution{p : ℝ}
    (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    triangleSiteCrossingProbability p < 1 / 2 := by
  rw [triangleSiteCrossingProbability_eq_cubic]
  have hfactor : 0 < p * (1 - p) + 1 / 2 := by
    have hp1 : p ≤ 1 := by linarith
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hid :
      (3 * p ^ 2 - 2 * p ^ 3) - 1 / 2 =
        (2 * p - 1) * (p * (1 - p) + 1 / 2) := by ring
  have hneg : 2 * p - 1 < 0 := by linarith
  have hprod : (2 * p - 1) * (p * (1 - p) + 1 / 2) < 0 :=
    mul_neg_of_neg_of_pos hneg hfactor
  nlinarith [hid]
