-- Prove2me | Theorems.Thm_ThreeCubes_card_admissible_block
-- name    : ThreeCubes.card_admissible_block
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:10:52.677671+00:00
-- url     : https://prove2.me/theorems/7d776c93-6bae-404d-9153-c1a457a87b98
-- title:
--   In each block of nine consecutive residues exactly seven avoid `±4 mod 9`.
-- statement:
--   In each block of nine consecutive residues exactly seven avoid `±4 mod 9`.
--
--   ```lean
--   theorem ThreeCubes.card_admissible_block(N : ℕ) :
--       ((Finset.range (9 * N)).filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5)).card = 7 * N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Density.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Density.lean#L22

-- Thm stub generated from Probability/Density.lean
import Mathlib
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

theorem ThreeCubes.card_admissible_block(N : ℕ) :
    ((Finset.range (9 * N)).filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5)).card = 7 * N := by sorry
