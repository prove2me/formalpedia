-- Prove2me | Definitions.Def_Geometry_HyperbolicBerggrenDensity
-- name    : Geometry_HyperbolicBerggrenDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:24.286031+00:00
-- url     : https://prove2.me/theorems/cf5b2adf-1d03-4310-8508-12753cf921a7
-- title:
--   Aether Catalog definitions — Geometry_HyperbolicBerggrenDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HyperbolicBerggrenDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HyperbolicBerggrenDensity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII

/-!
# Hyperbolic–Pythagorean Geodesics, cycle III: quadratic ball growth

The first cycle proved that the hyperbolic ball of radius `R` around `i` contains at least
`e^{R-2} - 1` Berggren nodes, and conjectured (sub-conjecture **C1-lite**) the true order
`e^{2R}`: the number of nodes should grow like the *hypotenuse*, not like its square root.

This file proves that conjecture.  The obstruction is arithmetic, not geometric: one has to
produce quadratically many *coprime* pairs of opposite parity, which requires a sieve.

## Main results

* `card_multiples_Ioc` : the exact count of multiples of `k` in an interval `(a, b]`.
* `sum_inv_sq_odd`, `sum_inv_odd` : two telescoping estimates,
  `∑_{i<n} 1/(2i+3)² ≤ 1/4` and `∑_{i<n} 1/(2i+3) ≤ √(2n+1) - 1`.
* `card_seedBox_lower` : **the sieve bound.**  For `K ≥ 256` the box
  `{m even, 2K < m ≤ 4K} × {n odd, 1 ≤ n ≤ 2K}` contains at least `K²/4` Euclid seeds.
* `hyperbolic_ball_quadratic_growth` : **C1-lite, closed.**  For every `K ≥ 256` the
  hyperbolic ball of radius `R = log K + 2` around the base point contains at least
  `e^{2R}/300` distinct Berggren nodes.  Since every node with hypotenuse `c` sits at
  distance `≈ ½ log c`, this is the true order of growth, and it shows definitively that
  geodesic search through the Berggren tree cannot beat exhaustive search: the ball that
  is guaranteed to contain a colliding pair for `N` already contains `≍ N` nodes.
-/

namespace HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/

/-- Even numbers in `(2K, 4K]`. -/
def evenBox (K : ℕ) : Finset ℕ := (Finset.Ioc (2 * K) (4 * K)).filter (fun m => 2 ∣ m)

/-- Odd numbers in `[1, 2K]`. -/
def oddBox (K : ℕ) : Finset ℕ := (Finset.Icc 1 (2 * K)).filter (fun n => ¬ 2 ∣ n)

/-- The coprime pairs of the box: genuine Euclid seeds. -/
def seedBox (K : ℕ) : Finset (ℕ × ℕ) :=
  ((evenBox K) ×ˢ (oddBox K)).filter (fun p => Nat.Coprime p.1 p.2)

/-- The possible odd common divisors. -/
def oddDivs (K : ℕ) : Finset ℕ := (Finset.Icc 3 (2 * K)).filter (fun d => ¬ 2 ∣ d)








/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/

/-- The hyperbolic point attached to a pair, extended by a default value. -/
def nodePoint (p : ℕ × ℕ) : ℍ :=
  if h : 0 < p.1 then hpoint p.1 p.2 h else UpperHalfPlane.I




/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/



end

end HyperbolicBerggrenGeodesics


