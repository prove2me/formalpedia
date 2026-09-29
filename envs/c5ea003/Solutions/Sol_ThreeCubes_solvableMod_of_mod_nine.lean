-- Prove2me | solution 1 for ThreeCubes.solvableMod_of_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:51:11.101164+00:00
-- url     : https://prove2.me/submissions/bfdb962b-a607-4f66-9e4b-2668d0c9a821

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_solvableMod_mul
import Theorems.Thm_ThreeCubes_solvableMod_prime_pow_ne_three
import Theorems.Thm_ThreeCubes_solvableMod_three_pow_aux

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






/-! ### Step 2: Hensel lifting away from `3` -/




/-! ### Step 3: the ramified prime `3` -/



/-! ### Step 4: solvability modulo prime powers -/



/-- **No obstruction beyond `9` at the prime `3`.**  If `n ≢ ±4 (mod 9)` then `n` is a sum of
three cubes modulo every power of `3`. -/
theorem solvableMod_three_pow (n : ℤ) (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5) (k : ℕ) :
    SolvableMod (3 ^ k) n := by
  have h9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨
      n % 9 = 8 := by omega
  rcases h9 with h | h | h | h | h | h | h
  · exact solvableMod_three_pow_aux n 1 0 (-1) (Or.inr rfl) (by omega) k
  · exact solvableMod_three_pow_aux n 0 0 1 (Or.inl rfl) (by omega) k
  · exact solvableMod_three_pow_aux n 1 0 1 (Or.inl rfl) (by omega) k
  · exact solvableMod_three_pow_aux n 1 1 1 (Or.inl rfl) (by omega) k
  · exact solvableMod_three_pow_aux n (-1) (-1) (-1) (Or.inr rfl) (by omega) k
  · exact solvableMod_three_pow_aux n (-1) 0 (-1) (Or.inr rfl) (by omega) k
  · exact solvableMod_three_pow_aux n 0 0 (-1) (Or.inr rfl) (by omega) k

/-! ### Step 5: the Chinese remainder theorem -/



/-! ### Main theorem -/





open ThreeCubes in
theorem solution(n : ℤ) (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5) :
    ∀ m : ℕ, 0 < m → SolvableMod m n := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      by_cases h3 : p = 3
      · subst h3; exact solvableMod_three_pow n h4 h5 k
      · exact solvableMod_prime_pow_ne_three p hp h3 n k
  | zero => intro h; exact absurd h (by omega)
  | one => intro _; exact ⟨0, 0, 0, by simp⟩
  | coprime a b ha hb hab iha ihb =>
      intro _
      exact solvableMod_mul hab (iha (by omega)) (ihb (by omega))
