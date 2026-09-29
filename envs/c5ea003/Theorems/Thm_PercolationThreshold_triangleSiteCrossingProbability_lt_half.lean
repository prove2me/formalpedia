-- Prove2me | Theorems.Thm_PercolationThreshold_triangleSiteCrossingProbability_lt_half
-- name    : PercolationThreshold.triangleSiteCrossingProbability_lt_half
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:47:52.321717+00:00
-- url     : https://prove2.me/theorems/1fc0271c-bfe7-478a-bcbc-a605834b1a92
-- title:
--   Below density `1/2`, the local triangular crossing probability is strictly
-- statement:
--   Below density `1/2`, the local triangular crossing probability is strictly
--   below `1/2`.
--
--   ```lean
--   theorem PercolationThreshold.triangleSiteCrossingProbability_lt_half{p : ℝ}
--       (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
--       triangleSiteCrossingProbability p < 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PercolationThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PercolationThreshold.lean#L67

-- Thm stub generated from Probability/PercolationThreshold.lean
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

theorem PercolationThreshold.triangleSiteCrossingProbability_lt_half{p : ℝ}
    (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    triangleSiteCrossingProbability p < 1 / 2 := by sorry
