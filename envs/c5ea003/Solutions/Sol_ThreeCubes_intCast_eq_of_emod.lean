-- Prove2me | solution 1 for ThreeCubes.intCast_eq_of_emod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:39:34.541008+00:00
-- url     : https://prove2.me/submissions/eff7319f-8002-41ee-a69c-ff6b1a80cbcf

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
theorem solution{n : ℤ} {r : ℤ} (h : n % 9 = r) : (n : ZMod 9) = (r : ZMod 9) := by
  have : n % (9 : ℤ) = r % (9 : ℤ) := by
    rw [h]
    have : r % (9 : ℤ) = r := by
      rw [← h]; exact Int.emod_emod_of_dvd n dvd_rfl
    rw [this]
  exact (ZMod.intCast_eq_intCast_iff' n r 9).mpr this
