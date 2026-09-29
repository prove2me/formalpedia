-- Prove2me | Definitions.Def_Algebra_CherryConfiguration
-- name    : Algebra_CherryConfiguration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:47.274506+00:00
-- url     : https://prove2.me/theorems/763e2f22-4a15-447a-a0c2-31defa17cf60
-- title:
--   Aether Catalog definitions — Algebra_CherryConfiguration
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CherryConfiguration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CherryConfiguration.lean by skeleton subtraction
import Mathlib

/-!
# Cherry configurations on cakes

We model `g` labelled cherries placed in `m` distinguishable admissible positions.  A valid
configuration has no collisions, hence is an embedding `Fin g ↪ Fin m`.  This gives an exact
finite probability model for the configuration-space part of pointed-cake moduli.  Separately,
we record the expected complex dimension `3g - 3 + n` of a genus-`g` surface carrying `n`
marked cherries.  The file does not claim to construct an algebraic moduli space.
-/

namespace CakeResearch

/-- Collision-free placements of `g` labelled cherries in `m` slots. -/
abbrev CherryConfiguration (g m : ℕ) := Fin g ↪ Fin m

/-
The exact number of collision-free cherry configurations is a falling factorial.
-/

/-
If there are fewer slots than cherries, collision-free placement is impossible.
-/

/-
If enough slots exist, at least one collision-free placement exists.
-/

/-- The probability of no collision under uniform independent placement in `m` slots.
The `m = 0` convention is harmless: there are no assignments unless `g = 0`. -/
def collisionFreeProbability (g m : ℕ) : ℚ :=
  (m.descFactorial g : ℚ) / (m ^ g : ℚ)

/-
Collision-free probability is never greater than one.
-/

/-
For a nonempty slot set, the collision-free probability vanishes exactly when there are
more cherries than slots.
-/

/-
With at most one cherry, collisions are impossible.
-/

/-
For a nonempty slot set, collisions are impossible with probability one exactly when
there is at most one cherry.
-/

/-- Expected complex dimension of the moduli of genus `g` cakes with `n` marked cherries. -/
def expectedModuliDimension (g n : ℤ) : ℤ := 3 * g - 3 + n

/-
Each additional cherry contributes one marked-point parameter.
-/

/-
Each additional handle contributes three complex parameters.
-/

/-
In the proposed unmarked model, the dimensions for genus two through five are
`3, 6, 9, 12`.
-/


/-
**Finite cherry-configuration theorem.**  For `g ≤ m`, collision-free configurations
exist, their exact number is `m(m-1)…(m-g+1)`, and their uniform probability is at most one.
This is the fully formal finite-probability result underlying the cherry-position model.
-/

end CakeResearch


