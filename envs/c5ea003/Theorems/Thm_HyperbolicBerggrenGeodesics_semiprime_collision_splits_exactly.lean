-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_semiprime_collision_splits_exactly
-- name    : HyperbolicBerggrenGeodesics.semiprime_collision_splits_exactly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:42.271687+00:00
-- url     : https://prove2.me/theorems/2e2a55eb-92e4-4bf3-8cdb-f7819503d56c
-- title:
--   Exact semiprime splitting (sub-conjecture D2-lite, closed).
-- statement:
--   **Exact semiprime splitting (sub-conjecture D2-lite, closed).**
--   If `N = p q` is a product of two primes and two distinct Berggren nodes carry the
--   hypotenuse `N`, then the two factors produced by `berggren_collision_splits` are exactly
--   `p` and `q`: a single collision fully factors the semiprime.  (The hypothesis `p ≠ q` that one
--   might expect turns out to be unnecessary: the argument only uses primality of `p` and `q`.)
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.semiprime_collision_splits_exactly{m₁ n₁ m₂ n₂ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
--       (hN₁ : m₁ ^ 2 + n₁ ^ 2 = p * q) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = p * q)
--       (hne : (m₁, n₁) ≠ (m₂, n₂)) :
--       (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = p ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = q) ∨
--         (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = q ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenDensity.lean#L486

-- Thm stub generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
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

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/












/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/





/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/

theorem HyperbolicBerggrenGeodesics.semiprime_collision_splits_exactly{m₁ n₁ m₂ n₂ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = p * q) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = p * q)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = p ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = q) ∨
      (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = q ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = p) := by sorry
