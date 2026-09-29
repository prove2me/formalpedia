-- Prove2me | Theorems.Thm_ThreeCubes_densitySevenNinths_iff_hasse
-- name    : ThreeCubes.densitySevenNinths_iff_hasse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:31.740675+00:00
-- url     : https://prove2.me/theorems/2ebd436f-f74b-4e0d-b583-074fd1d1c532
-- title:
--   The density statement is exactly the Hasse principle for nonnegative `n`.
-- statement:
--   **The density statement is exactly the Hasse principle for nonnegative `n`.**  So the
--   `7/9` density conjecture is not a statistical strengthening: it is equivalent to the
--   representability of every locally solvable nonnegative integer.
--
--   ```lean
--   theorem ThreeCubes.densitySevenNinths_iff_hasse:
--       DensitySevenNinths ↔ ∀ n : ℕ, (n : ℤ) % 9 ≠ 4 → (n : ℤ) % 9 ≠ 5 →
--         IsSumOfThreeCubes (n : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Density.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Density.lean#L78

-- Thm stub generated from Probability/Density.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Density

/-!
# Density of locally solvable and of representable integers

Combining the main local-solvability theorem with an exact count over each block of nine
consecutive integers we obtain:

* `ThreeCubes.card_locallySolvable_block` — exactly `7N` of the integers `0, …, 9N-1` are
  everywhere locally solvable, i.e. the locally solvable integers have density exactly `7/9`;
* `ThreeCubes.card_isSumOfThreeCubes_le` — consequently at most `7N` of them are actual sums
  of three cubes.  The conjecture of Heath-Brown asserts that this upper bound is attained
  (asymptotically), i.e. that the density of representable integers is exactly `7/9`; the
  formal statement `ThreeCubes.DensitySevenNinths` records that conjecture, and
  `ThreeCubes.densitySevenNinths_iff_hasse` shows it is *equivalent* to the Hasse principle
  for the affine cubic surface.
-/

open ThreeCubes

open Finset





open scoped Classical in

theorem ThreeCubes.densitySevenNinths_iff_hasse:
    DensitySevenNinths ↔ ∀ n : ℕ, (n : ℤ) % 9 ≠ 4 → (n : ℤ) % 9 ≠ 5 →
      IsSumOfThreeCubes (n : ℤ) := by sorry
