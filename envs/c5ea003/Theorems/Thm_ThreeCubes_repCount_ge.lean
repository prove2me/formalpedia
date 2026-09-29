-- Prove2me | Theorems.Thm_ThreeCubes_repCount_ge
-- name    : ThreeCubes.repCount_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:24.584238+00:00
-- url     : https://prove2.me/theorems/619fc894-bf44-4f15-911f-d9dc409da6e5
-- title:
--   Power-saving lower bound.
-- statement:
--   **Power-saving lower bound.**  At least `K⁵` of the integers in `[0, 9K⁹]` are sums of
--   three cubes; equivalently `repCount N ≫ N^{5/9}`.  Contrast with
--   `ThreeCubes.card_isSumOfThreeCubes_le`, which gives the upper bound `7N/9`.
--
--   ```lean
--   theorem ThreeCubes.repCount_ge(K : ℕ) : K ^ 5 ≤ repCount (9 * K ^ 9) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/LowerBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/LowerBounds.lean#L122

-- Thm stub generated from Probability/LowerBounds.lean
import Mathlib
import Definitions.Def_Probability_Density
import Definitions.Def_Probability_LowerBounds
import Definitions.Def_Probability_Rational

/-!
# Unconditional lower bounds for sums of three cubes

`Probability.ThreeCubes.Density` gives the *upper* bound: at most `7/9` of all integers are
sums of three cubes (`ThreeCubes.card_isSumOfThreeCubes_le`), and
`ThreeCubes.densitySevenNinths_iff_hasse` shows that the matching lower bound — i.e. density
exactly `7/9` — is *equivalent* to the Hasse principle for the affine cubic surface, hence
completely out of reach at present.

This file proves the strongest lower bound that is unconditional, namely a power-saving one.
Counting the values `k³ + m³` with `K³ ≤ k < 2K³` and `0 ≤ m ≤ K²`, the "small" cube `m³` is
always smaller than the gap `(k+1)³ - k³ = 3k² + 3k + 1`, so `k` is recoverable from the value
as `⌊n^{1/3}⌋` and the parametrisation is *injective*
(`ThreeCubes.cube_pair_inj`).  This produces `K³(K²+1)` distinct representable integers below
`9K⁹`, i.e.

* `ThreeCubes.repCount_ge` : `K⁵ ≤ repCount (9K⁹)`, an `≫ N^{5/9}` lower bound for the
  counting function `repCount N = #{n ≤ N : n is a sum of three cubes}`.

The exponent `5/9` is exactly the classical elementary bound: `3/9` comes from the cubes
themselves and the extra `2/9` from the `k^{2/3}`-many admissible small cubes.  Any improvement
beyond the trivial multiplicativity of this construction requires genuine control of the
representation multiplicity, which is the content of Conjecture 3 of `FUTURE_DIRECTIONS.md`.

The last section records the sharp contrast with the *rational* problem: four rational cubes
always suffice, by a one-line identity (`ThreeCubes.isSumOfFourRationalCubes`), whereas over
`ℤ` the analogous statement for four cubes is open.
-/

open ThreeCubes

open Finset

/-! ### An injective two-parameter family of sums of two cubes -/








open scoped Classical in

theorem ThreeCubes.repCount_ge(K : ℕ) : K ^ 5 ≤ repCount (9 * K ^ 9) := by sorry
