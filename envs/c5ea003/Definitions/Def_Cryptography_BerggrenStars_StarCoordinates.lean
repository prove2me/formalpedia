-- Prove2me | Definitions.Def_Cryptography_BerggrenStars_StarCoordinates
-- name    : Cryptography_BerggrenStars_StarCoordinates
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:11.300348+00:00
-- url     : https://prove2.me/theorems/6c06166d-fe32-4a89-84d2-8cdfc93f3d08
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenStars_StarCoordinates
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenStars.StarCoordinates`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenStars/StarCoordinates.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

/-!
# Star coordinates: the Berggren tree seen from the two boundary stars

`Cryptography.BerggrenStars.HypercycleStars` shows that a Berggren node `z(m,n) = (n+i)/m`
sits at distance `arsinh n` from the geodesic over the boundary point `0` and at distance
`arsinh (m-n)` from the geodesic over the boundary point `1`. So the pair

  `(u, v) = (n, m - n)`

is exactly the pair of *star indices* of the node — one index per radiating star. This file
develops the tree entirely in these coordinates, and the result is markedly cleaner than in
Euclid coordinates.

## Main results

* `starPoint_charges` : `(u, v)` really is the pair of hyperbolic star charges,
  `sinh d₀ = u` and `sinh d₁ = v`.
* `node_eq_of_charges` : **the two star charges determine the node**; the star picture is a
  faithful coordinate system on the tree.
* `isSeed_iff_isStarPair` : the Euclid-seed conditions `0 < n < m`, `gcd(m,n) = 1`, `m + n` odd
  become the conditions `0 < u`, `0 < v`, `gcd(u,v) = 1`, `v` odd.
* `isStarPair_starL/M/R` : the three Berggren moves act as
  `(u,v) ↦ (u+v, v)`, `(u,v) ↦ (u+v, 2u+v)`, `(u,v) ↦ (u, 2u+v)` and preserve star pairs.
* `exists_depth_of_isStarPair` : **completeness** — every star pair is reached from the root
  `(1,1)`, by a descent whose trichotomy is `u > v`, `u < v < 2u`, `v > 2u`.
* `starReaches_unique_depth` : **it is a tree** — the depth at which a star pair is reached is
  unique, so the depth function is well defined.
* `cosh_dist_starPoint` : the radial coordinate in star coordinates,
  `cosh d = ((u+v)² + u² + 1)/(2(u+v))`.
-/

namespace BerggrenHypercycleStars

open Real UpperHalfPlane

/-! ## Part 1. Star coordinates and their charges -/

/-- The half-plane node attached to the star-coordinate pair `(u, v)`: it is the Euclid seed
`(m, n) = (u + v, u)`. -/
noncomputable def starPoint (u v : ℕ) (h : 0 < u + v) : ℍ := hpoint (u + v) u h



/-- A **star pair**: the star-coordinate description of a Euclid seed. -/
structure IsStarPair (u v : ℕ) : Prop where
  posu : 0 < u
  posv : 0 < v
  cop : Nat.Coprime u v
  odd : v % 2 = 1




/-! ## Part 2. The three Berggren moves in star coordinates -/

/-- `B₁` in star coordinates. -/
def starL (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + p.2, p.2)

/-- `B₂` in star coordinates. -/
def starM (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + p.2, 2 * p.1 + p.2)

/-- `B₃` in star coordinates. -/
def starR (p : ℕ × ℕ) : ℕ × ℕ := (p.1, 2 * p.1 + p.2)




/-! ## Part 3. Reachability: completeness and uniqueness of depth -/

/-- `StarReaches p k` : the star pair `p` is obtained from the root `(1,1)` (the seed `(2,1)`,
i.e. the triple `(3,4,5)`) by exactly `k` Berggren moves. -/
inductive StarReaches : ℕ × ℕ → ℕ → Prop
  | root : StarReaches (1, 1) 0
  | l {p k} : StarReaches p k → StarReaches (starL p) (k + 1)
  | m {p k} : StarReaches p k → StarReaches (starM p) (k + 1)
  | r {p k} : StarReaches p k → StarReaches (starR p) (k + 1)








/-! ## Part 4. The radial coordinate in star coordinates -/



end BerggrenHypercycleStars


