-- Prove2me | solution 1 for ThreeCubes.cube_lift_three_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:34:55.153585+00:00
-- url     : https://prove2.me/submissions/21ff00e1-2491-4dd5-b547-866dfc413424

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic

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
theorem solution(a x : ℤ) (hx : ¬ (3 : ℤ) ∣ x) (j : ℕ)
    (h : (3 : ℤ) ^ (j + 2) ∣ x ^ 3 - a) :
    ∃ x' : ℤ, (3 : ℤ) ^ (j + 3) ∣ x' ^ 3 - a ∧ (3 : ℤ) ∣ x' - x := by
  obtain ⟨s, hs⟩ := h
  have hsq : (3 : ℤ) ∣ x ^ 2 - 1 := by
    have h3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    obtain ⟨q, hq⟩ : ∃ q, x = 3 * q + x % 3 := ⟨x / 3, by omega⟩
    rcases h3 with h3 | h3 | h3
    · exact absurd ⟨x / 3, by omega⟩ hx
    · exact ⟨3 * q ^ 2 + 2 * q, by rw [hq, h3]; ring⟩
    · exact ⟨3 * q ^ 2 + 4 * q + 1, by rw [hq, h3]; ring⟩
  obtain ⟨w, hw⟩ := hsq
  refine ⟨x + (-s) * (3 : ℤ) ^ (j + 1), ?_, ⟨(-s) * 3 ^ j, by ring⟩⟩
  refine ⟨-s * w + x * s ^ 2 * 3 ^ j - s ^ 3 * 3 ^ (2 * j), ?_⟩
  have h2 : x ^ 2 = 1 + 3 * w := by linarith [hw]
  linear_combination hs + ((3 : ℤ) ^ (j + 2) * (-s)) * h2
