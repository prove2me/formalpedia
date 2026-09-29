-- Prove2me | solution 1 for ThreeCubes.not_locallySolvable_of_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:33.423934+00:00
-- url     : https://prove2.me/submissions/d5a70b1e-4e76-4bc4-9208-31755d11dcc8

-- Sol generated from Probability/Basic.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_not_solvableMod_nine

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
theorem solution{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) :
    ¬ LocallySolvable n := fun hL => not_solvableMod_nine h (hL 9 (by norm_num))
