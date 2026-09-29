-- Prove2me | Definitions.Def_Applications_HyperbolicNumberTheory_CayleyPythagoreanBridge
-- name    : Applications_HyperbolicNumberTheory_CayleyPythagoreanBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:02.487442+00:00
-- url     : https://prove2.me/theorems/f15eb6f7-9879-4b75-b8f2-a59a28574e47
-- title:
--   Aether Catalog definitions — Applications_HyperbolicNumberTheory_CayleyPythagoreanBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.HyperbolicNumberTheory.CayleyPythagoreanBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/HyperbolicNumberTheory/CayleyPythagoreanBridge.lean by skeleton subtraction
import Mathlib

/-!
# Modular cusp orbits, horocycles, and Pythagorean triples

Integer translations of `i` in the upper half-plane become, under the Cayley
transform, the points `n/(n+2i)` of the Poincaré disk.  This file proves that
this modular orbit lies on the horocycle `|2z-1| = 1`.  After clearing
coordinates, the same identity is exactly Euclid's Pythagorean identity

`(n² - 4)² + (4n)² = (n² + 4)²`.

Thus one algebraic equation simultaneously describes a geometric cusp orbit
and an infinite family of integral right triangles.
-/

namespace HyperbolicNumberTheory

open Complex

/-- Cayley image of the modular translation orbit `n + i`. -/
noncomputable def cayleyModularOrbit (n : ℤ) : ℂ :=
  (n : ℂ) / ((n : ℂ) + 2 * I)

/-
Exact real coordinate of the Cayley-transformed modular orbit.
-/

/-
Exact imaginary coordinate of the Cayley-transformed modular orbit.
-/

/-
Every finite modular translate is strictly inside the Poincaré disk.
-/

/-
The modular translation orbit lies on the horocycle centered at `1/2`
with Euclidean radius `1/2`, tangent to the ideal boundary at `1`.
-/

/-
Euclid's Pythagorean identity in the normalization naturally supplied by
Cayley transformation of the modular orbit.
-/

/-
**Cayley–Pythagorean connector.**  The same integer parameter `n` determines
both a point of a modular cusp orbit on a Poincaré-disk horocycle and an
integral Pythagorean triple.  The first conjunct is genuinely geometric; the
second is the cleared-denominator arithmetic shadow of its circle equation.
-/


end HyperbolicNumberTheory


