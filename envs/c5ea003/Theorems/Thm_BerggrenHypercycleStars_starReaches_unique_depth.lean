-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_starReaches_unique_depth
-- name    : BerggrenHypercycleStars.starReaches_unique_depth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:35:01.351334+00:00
-- url     : https://prove2.me/theorems/63130212-606c-41d0-9fef-ad37b4697dd0
-- title:
--   The Berggren tree really is a tree, in star coordinates.
-- statement:
--   **The Berggren tree really is a tree, in star coordinates.** A star pair is reached at
--   exactly one depth, so the depth function is well defined on primitive Pythagorean triples.
--   The proof is the disjointness of the three move-images, which is precisely the trichotomy
--   `u > v` / `u < v < 2u` / `v > 2u` of the descent.
--
--   ```lean
--   theorem BerggrenHypercycleStars.starReaches_unique_depth: ∀ s : ℕ, ∀ p : ℕ × ℕ, p.1 + p.2 ≤ s → ∀ j k : ℕ,
--       StarReaches p j → StarReaches p k → j = k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/StarCoordinates.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/StarCoordinates.lean#L239

-- Thm stub generated from Cryptography/BerggrenStars/StarCoordinates.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_StarCoordinates

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

open BerggrenHypercycleStars

open Real UpperHalfPlane

/-! ## Part 1. Star coordinates and their charges -/








/-! ## Part 2. The three Berggren moves in star coordinates -/







/-! ## Part 3. Reachability: completeness and uniqueness of depth -/

theorem BerggrenHypercycleStars.starReaches_unique_depth: ∀ s : ℕ, ∀ p : ℕ × ℕ, p.1 + p.2 ≤ s → ∀ j k : ℕ,
    StarReaches p j → StarReaches p k → j = k := by sorry
