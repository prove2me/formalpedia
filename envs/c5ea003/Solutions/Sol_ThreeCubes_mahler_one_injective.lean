-- Prove2me | solution 1 for ThreeCubes.mahler_one_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:25:30.097278+00:00
-- url     : https://prove2.me/submissions/6e96958d-db78-4758-b433-d51d2bf927f8

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
theorem solution: Function.Injective
    (fun t : ℤ => ((9 * t ^ 4 : ℤ), (3 * t - 9 * t ^ 4 : ℤ), (1 - 9 * t ^ 3 : ℤ))) := by
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  have h : (1 : ℤ) - 9 * a ^ 3 = 1 - 9 * b ^ 3 := hab.2.2
  have h3 : a ^ 3 = b ^ 3 := by linarith
  exact Odd.strictMono_pow (R := ℤ) (by decide) |>.injective h3
