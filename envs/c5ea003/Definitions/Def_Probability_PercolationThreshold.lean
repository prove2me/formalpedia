-- Prove2me | Definitions.Def_Probability_PercolationThreshold
-- name    : Probability_PercolationThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:53.747523+00:00
-- url     : https://prove2.me/theorems/702807d9-9f58-4eef-9004-9597a56e299f
-- title:
--   Aether Catalog definitions — Probability_PercolationThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PercolationThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PercolationThreshold.lean by skeleton subtraction
import Mathlib

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

namespace PercolationThreshold

/-- The probability that at least two of three independent sites of density `p`
are open: either all three are open, or exactly two are open. -/
def triangleSiteCrossingProbability (p : ℝ) : ℝ :=
  p ^ 3 + 3 * p ^ 2 * (1 - p)









/-- A local critical parameter is a Bernoulli parameter in `[0,1]` at which the
three-site crossing event is fair. -/
def IsTriangularSiteLocalCritical (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ triangleSiteCrossingProbability p = 1 / 2


/-- For bond percolation on one triangular face, all three vertices are connected
exactly when either exactly two or all three of its bonds are open. -/
def triangleBondSpanningProbability (p : ℝ) : ℝ :=
  3 * p ^ 2 * (1 - p) + p ^ 3



end PercolationThreshold


