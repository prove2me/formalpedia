-- Prove2me | solution 1 for ThreeCubes.three_cubes_mod_prime_unit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:46:54.638915+00:00
-- url     : https://prove2.me/submissions/3d9bfa80-e043-491d-a5fe-80a6bd781819

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_three_cubes_surjective_mod_prime

/-!
# The mod 9 congruence is the only local obstruction for sums of three cubes

The main theorem of this file, `ThreeCubes.locallySolvable_iff`, states

  `LocallySolvable n ↔ (n % 9 ≠ 4 ∧ n % 9 ≠ 5)`,

i.e. the congruence `x³ + y³ + z³ ≡ n (mod m)` is solvable for *every* modulus `m > 0`
precisely when the single classical obstruction modulo `9` is absent.  Equivalently the
affine cubic surface `x³ + y³ + z³ = n` has `ℤ_p`-points for every prime `p` exactly when
`n ≢ ±4 (mod 9)`.

The proof combines three ingredients from rather different areas:

* **Additive combinatorics.** The Cauchy–Davenport theorem applied to the set of cubes
  `C ⊆ 𝔽_p` (which satisfies `3|C| ≥ p + 2` because the cubing map is at most `3`-to-`1`
  away from `0` and exactly `1`-to-`1` at `0`) shows `C + C + C = 𝔽_p`; see
  `three_cubes_surjective_mod_prime`.
* **Hensel lifting at unramified primes.** For `p ≠ 3` a solution mod `p` with one
  coordinate a unit lifts to every `p^k`; see `cube_lift`.
* **A ramified analysis at `p = 3`.** The derivative `3x²` has valuation exactly one, so the
  naive Hensel step fails; instead one lifts a unit `u ≡ 1 (mod 9)` to a cube modulo every
  power of `3` (`cube_lift_three`), and then a small case analysis over the seven admissible
  residues mod `9` produces the required representation.

Finally the Chinese remainder theorem glues the prime powers together.
-/

open ThreeCubes

open Finset Pointwise Polynomial

/-! ### Step 1: sums of three cubes cover `𝔽_p` (Cauchy–Davenport) -/




theorem exists_intCast (p : ℕ) (a : ZMod p) : ∃ x : ℤ, (x : ZMod p) = a :=
  ⟨ZMod.cast a, ZMod.intCast_zmod_cast a⟩


/-! ### Step 2: Hensel lifting away from `3` -/




/-! ### Step 3: the ramified prime `3` -/



/-! ### Step 4: solvability modulo prime powers -/




/-! ### Step 5: the Chinese remainder theorem -/



/-! ### Main theorem -/





open ThreeCubes in
theorem solution(p : ℕ) (hp : p.Prime) (n : ℤ) :
    ∃ x y z : ℤ, (p : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n ∧ ¬ (p : ℤ) ∣ x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ∀ w : ℤ, ((p : ℤ) ∣ w) ↔ ((w : ZMod p) = 0) :=
    fun w => (ZMod.intCast_zmod_eq_zero_iff_dvd w p).symm
  suffices h : ∃ X Y Z : ZMod p, X ^ 3 + Y ^ 3 + Z ^ 3 = (n : ZMod p) ∧ X ≠ 0 by
    obtain ⟨X, Y, Z, hsum, hX⟩ := h
    obtain ⟨x, rfl⟩ := exists_intCast p X
    obtain ⟨y, rfl⟩ := exists_intCast p Y
    obtain ⟨z, rfl⟩ := exists_intCast p Z
    refine ⟨x, y, z, ?_, ?_⟩
    · rw [hcast]; push_cast; linear_combination hsum
    · rw [hcast]; exact hX
  by_cases ha : (n : ZMod p) = 0
  · exact ⟨1, -1, 0, by rw [ha]; ring, one_ne_zero⟩
  · obtain ⟨X, Y, Z, hsum⟩ := three_cubes_surjective_mod_prime p (n : ZMod p)
    by_cases hX : X ≠ 0
    · exact ⟨X, Y, Z, hsum, hX⟩
    by_cases hY : Y ≠ 0
    · exact ⟨Y, X, Z, by rw [← hsum]; ring, hY⟩
    by_cases hZ : Z ≠ 0
    · exact ⟨Z, X, Y, by rw [← hsum]; ring, hZ⟩
    push_neg at hX hY hZ
    exact absurd (by rw [← hsum, hX, hY, hZ]; ring) ha
