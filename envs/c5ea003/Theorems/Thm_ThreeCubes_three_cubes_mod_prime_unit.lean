-- Prove2me | Theorems.Thm_ThreeCubes_three_cubes_mod_prime_unit
-- name    : ThreeCubes.three_cubes_mod_prime_unit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:05.604123+00:00
-- url     : https://prove2.me/theorems/54fca32e-011a-4a8e-b1f2-55b5497328ec
-- title:
--   Refinement of `three_cubes_surjective_mod_prime`: one may always take the first summand
-- statement:
--   Refinement of `three_cubes_surjective_mod_prime`: one may always take the first summand
--   to be a unit.  This is what makes Hensel lifting applicable.
--
--   ```lean
--   theorem ThreeCubes.three_cubes_mod_prime_unit(p : ℕ) (hp : p.Prime) (n : ℤ) :
--       ∃ x y z : ℤ, (p : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n ∧ ¬ (p : ℤ) ∣ x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/LocalSolvability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/LocalSolvability.lean#L112

-- Thm stub generated from Probability/LocalSolvability.lean
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

theorem ThreeCubes.three_cubes_mod_prime_unit(p : ℕ) (hp : p.Prime) (n : ℤ) :
    ∃ x y z : ℤ, (p : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n ∧ ¬ (p : ℤ) ∣ x := by sorry
