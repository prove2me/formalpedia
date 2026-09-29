-- Prove2me | Theorems.Thm_BerggrenRationalStars_isSeed_along_unit_ray
-- name    : BerggrenRationalStars.isSeed_along_unit_ray
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:35:10.339764+00:00
-- url     : https://prove2.me/theorems/c9dd7d5e-2be4-41ea-87cc-756d5a28aee1
-- title:
--   The unit rays are the brightest lines of every rational star.
-- statement:
--   **The unit rays are the brightest lines of every rational star.** If a node has charge `±1`
--   at `p/q` (with `p < q`), then *every* second lattice point along its ray is again a Berggren
--   node: `(m + 2tq, n + 2tp)` is a Euclid seed for all `t`. No coprimality sieve thins these
--   rays out — the only constraint is parity, and translating by `2(q,p)` preserves it.
--
--   ```lean
--   theorem BerggrenRationalStars.isSeed_along_unit_ray(p q m n t : ℕ) (hpq : p < q) (h : IsSeed m n)
--       (hk : starCharge p q m n = 1 ∨ starCharge p q m n = -1) :
--       IsSeed (m + 2 * t * q) (n + 2 * t * p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/RationalStarRays.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/RationalStarRays.lean#L78

-- Thm stub generated from Cryptography/BerggrenStars/RationalStarRays.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars

/-!
# The individual rays of a rational star: straight lines, shrinking steps, ideal tips

`Cryptography.BerggrenStars.RationalStars` determines *which* rays of the pencil over a
boundary rational `p/q` are populated by Berggren nodes. This file studies a single ray.

Fix a boundary rational `p/q` and a star charge `k = q n - p m`. The nodes of charge `k` are
exactly the lattice translates `(m + t q, n + t p)` of one another, and here we prove that they
form the visible radial line of the picture:

## Main results

* `star_ray_line` : the exact Euclidean equation of the ray,
  `Re z = p/q + (k/q) · Im z`. Charge `k` is the Euclidean line parameter.
* `ray_constant_distVLine` : two nodes of equal charge are at equal hyperbolic distance from
  the geodesic over `p/q` — the ray is a hypercycle, not a geodesic.
* `dvd_charge_of_common_divisor`, `isSeed_along_unit_ray` : the arithmetic of a ray. Any common
  divisor of the two coordinates of a node divides its charge; consequently the two **unit
  rays** `k = ±1` of every rational star are *fully* populated — every second lattice point on
  them is a Berggren node. These are the brightest lines of the star.
* `cross_along_ray` : the seed cross product of two nodes on a ray of charge `k` at lattice
  distance `t` is exactly `t k`; the charge is the symplectic area form of the ray.
* `cosh_step_along_star_ray` : hence the exact hyperbolic step length along the ray,
  `cosh(step) = ((tk)² + m² + m'²)/(2 m m')`.
* `step_along_star_ray_tendsto_zero` : the steps along a ray tend to `0`. A ray is an infinite
  path of shrinking steps — the reason it renders as a smooth straight line rather than as a
  sequence of separated dots.
* `ray_tendsto_boundary` : the ray converges to its ideal tip `p/q`. Every rational boundary
  point is the limit of the ray(s) of its own star.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars Real UpperHalfPlane

/-! ## Part 1. The ray is a Euclidean straight line through `p/q`, and a hypercycle -/



/-! ## Part 2. The arithmetic of a ray: the unit rays are fully populated -/

theorem BerggrenRationalStars.isSeed_along_unit_ray(p q m n t : ℕ) (hpq : p < q) (h : IsSeed m n)
    (hk : starCharge p q m n = 1 ∨ starCharge p q m n = -1) :
    IsSeed (m + 2 * t * q) (n + 2 * t * p) := by sorry
