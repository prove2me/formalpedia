-- Prove2me | Definitions.Def_Probability_Basic
-- name    : Probability_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:35.805906+00:00
-- url     : https://prove2.me/theorems/8b2a5f14-7c9e-4669-8a7b-084d25206b3f
-- title:
--   Aether Catalog definitions — Probability_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Basic.lean by skeleton subtraction
import Mathlib

/-!
# Sums of three cubes: basic theory, the mod 9 obstruction, and parametric families

This file sets up the arithmetic of the affine cubic surface
`x³ + y³ + z³ = n` over `ℤ`.

Main contents.

* `ThreeCubes.IsSumOfThreeCubes` — the predicate `∃ x y z : ℤ, x³ + y³ + z³ = n`.
* `ThreeCubes.SolvableMod` / `ThreeCubes.LocallySolvable` — solvability of the
  congruence `x³ + y³ + z³ ≡ n (mod m)`, for one modulus and for all moduli.
* `ThreeCubes.not_isSumOfThreeCubes_of_mod_nine` — the classical congruence
  obstruction: `n ≡ ±4 (mod 9)` is never a sum of three cubes.
* Closure properties: negation, cubic scaling, translation by a cube.
* Two classical one-parameter families showing that `1` and `2` have infinitely
  many representations, and hence that the representation-counting function is
  unbounded.

The deeper statement that `n ≢ ±4 (mod 9)` is the *only* obstruction to local
solvability is proved in `Probability.ThreeCubes.LocalSolvability`.
-/

namespace ThreeCubes

/-- `n` is a sum of three integer cubes. -/
def IsSumOfThreeCubes (n : ℤ) : Prop := ∃ x y z : ℤ, x ^ 3 + y ^ 3 + z ^ 3 = n

/-- The congruence `x³ + y³ + z³ ≡ n (mod m)` is solvable. -/
def SolvableMod (m : ℕ) (n : ℤ) : Prop := ∃ x y z : ℤ, (m : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n

/-- `n` is *locally solvable*: the congruence `x³ + y³ + z³ ≡ n` is solvable modulo every
positive modulus. Equivalently (by the Chinese remainder theorem and compactness) the affine
surface has a `ℤ_p`-point for every prime `p`. -/
def LocallySolvable (n : ℤ) : Prop := ∀ m : ℕ, 0 < m → SolvableMod m n

/-! ### Elementary closure properties -/






/-! ### The mod 9 obstruction -/








/-! ### Parametric families -/







end ThreeCubes


