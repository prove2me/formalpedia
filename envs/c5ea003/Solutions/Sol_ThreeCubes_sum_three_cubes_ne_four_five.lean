-- Prove2me | solution 1 for ThreeCubes.sum_three_cubes_ne_four_five
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:39:35.113863+00:00
-- url     : https://prove2.me/submissions/58b844c1-ace1-49f3-ad5b-3c1754843494

-- Sol generated from Probability/Basic.lean
import Mathlib
import Definitions.Def_Probability_Basic

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

open ThreeCubes




/-! ### Elementary closure properties -/






/-! ### The mod 9 obstruction -/








/-! ### Parametric families -/








open ThreeCubes in
theorem solution(x y z : ZMod 9) :
    x ^ 3 + y ^ 3 + z ^ 3 ≠ 4 ∧ x ^ 3 + y ^ 3 + z ^ 3 ≠ 5 := by decide +revert
