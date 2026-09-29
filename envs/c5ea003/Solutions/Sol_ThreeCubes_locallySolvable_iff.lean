-- Prove2me | solution 1 for ThreeCubes.locallySolvable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:51.387874+00:00
-- url     : https://prove2.me/submissions/83d7258b-10c0-418c-8aba-6e58207f7971

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_not_locallySolvable_of_mod_nine
import Theorems.Thm_ThreeCubes_solvableMod_of_mod_nine

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




/-! ### Step 5: the Chinese remainder theorem -/



/-! ### Main theorem -/





open ThreeCubes in
theorem solution(n : ℤ) : LocallySolvable n ↔ (n % 9 ≠ 4 ∧ n % 9 ≠ 5) := by
  constructor
  · intro h
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · exact not_locallySolvable_of_mod_nine (Or.inl hc) h
    · exact not_locallySolvable_of_mod_nine (Or.inr hc) h
  · rintro ⟨h4, h5⟩
    exact solvableMod_of_mod_nine n h4 h5
