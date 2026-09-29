-- Prove2me | solution 1 for ThreeCubes.cube_lift_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:37:08.569594+00:00
-- url     : https://prove2.me/submissions/b3a7bf7e-7311-46c4-835a-94515e46903a

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_cube_lift_three_step

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
theorem solution(a : ℤ) (ha : (9 : ℤ) ∣ a - 1) (k : ℕ) :
    ∃ x : ℤ, (3 : ℤ) ^ k ∣ x ^ 3 - a := by
  have key : ∀ j : ℕ, ∃ x : ℤ, ¬ (3 : ℤ) ∣ x ∧ (3 : ℤ) ^ (j + 2) ∣ x ^ 3 - a := by
    intro j
    induction j with
    | zero =>
        refine ⟨1, by decide, ?_⟩
        obtain ⟨c, hc⟩ := ha
        exact ⟨-c, by rw [show (1 : ℤ) ^ 3 - a = -(a - 1) by ring, hc]; norm_num⟩
    | succ i ih =>
        obtain ⟨x, hx, hdvd⟩ := ih
        obtain ⟨x', h1, h2⟩ := cube_lift_three_step a x hx i hdvd
        refine ⟨x', fun hcon => hx ?_, h1⟩
        obtain ⟨d, hd⟩ := h2
        obtain ⟨e, he⟩ := hcon
        exact ⟨e - d, by linarith⟩
  obtain ⟨x, _, hdvd⟩ := key k
  exact ⟨x, dvd_trans (pow_dvd_pow 3 (by omega)) hdvd⟩
