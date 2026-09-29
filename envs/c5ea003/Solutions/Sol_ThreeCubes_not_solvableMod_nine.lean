-- Prove2me | solution 1 for ThreeCubes.not_solvableMod_nine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:50.397899+00:00
-- url     : https://prove2.me/submissions/5a60ea21-82bd-4b43-99dd-0e5c8d9e1fc0

-- Sol generated from Probability/Basic.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_intCast_eq_of_emod
import Theorems.Thm_ThreeCubes_sum_three_cubes_ne_four_five

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
theorem solution{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) : ¬ SolvableMod 9 n := by
  rintro ⟨x, y, z, hd⟩
  have hcast : ((x ^ 3 + y ^ 3 + z ^ 3 - n : ℤ) : ZMod 9) = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr (by exact_mod_cast hd)
  push_cast at hcast
  have hn : ((x : ZMod 9) ^ 3 + (y : ZMod 9) ^ 3 + (z : ZMod 9) ^ 3) = (n : ZMod 9) := by
    linear_combination hcast
  rcases h with h | h
  · have := intCast_eq_of_emod h
    rw [this] at hn
    exact (sum_three_cubes_ne_four_five (x : ZMod 9) y z).1 (by rw [hn]; norm_num)
  · have := intCast_eq_of_emod h
    rw [this] at hn
    exact (sum_three_cubes_ne_four_five (x : ZMod 9) y z).2 (by rw [hn]; norm_num)
