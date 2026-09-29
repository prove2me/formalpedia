-- Prove2me | Theorems.Thm_ThreeCubes_cube_pair_inj
-- name    : ThreeCubes.cube_pair_inj
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:11:55.367034+00:00
-- url     : https://prove2.me/theorems/431c92b3-90e0-46c2-a834-4d980def791c
-- title:
--   Injectivity of the parametrisation `(k, m) ↦ k³ + m³` on the range
-- statement:
--   **Injectivity of the parametrisation `(k, m) ↦ k³ + m³`** on the range
--   `K³ ≤ k < 2K³`, `m ≤ K²`.  Indeed the value determines `k` (it lies in `[k³, (k+1)³)`) and
--   then `m`.
--
--   ```lean
--   theorem ThreeCubes.cube_pair_inj{K k m k' m' : ℕ} (hk : K ^ 3 ≤ k) (hm : m ≤ K ^ 2)
--       (hk' : K ^ 3 ≤ k') (hm' : m' ≤ K ^ 2) (h : k ^ 3 + m ^ 3 = k' ^ 3 + m' ^ 3) :
--       k = k' ∧ m = m' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/LowerBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/LowerBounds.lean#L47

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

theorem ThreeCubes.cube_pair_inj{K k m k' m' : ℕ} (hk : K ^ 3 ≤ k) (hm : m ≤ K ^ 2)
    (hk' : K ^ 3 ≤ k') (hm' : m' ≤ K ^ 2) (h : k ^ 3 + m ^ 3 = k' ^ 3 + m' ^ 3) :
    k = k' ∧ m = m' := by sorry
