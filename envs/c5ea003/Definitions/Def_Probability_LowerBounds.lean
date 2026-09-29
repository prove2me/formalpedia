-- Prove2me | Definitions.Def_Probability_LowerBounds
-- name    : Probability_LowerBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:09.008572+00:00
-- url     : https://prove2.me/theorems/2fbc19f8-30f9-456f-9d78-03d897f839db
-- title:
--   Aether Catalog definitions — Probability_LowerBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.LowerBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/LowerBounds.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Density
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

namespace ThreeCubes

open Finset

/-! ### An injective two-parameter family of sums of two cubes -/



/-- The set of values `k³ + m³` for `K³ ≤ k < 2K³` and `0 ≤ m ≤ K²`. -/
def cubeValues (K : ℕ) : Finset ℕ :=
  ((Finset.Ico (K ^ 3) (2 * K ^ 3)) ×ˢ (Finset.range (K ^ 2 + 1))).image
    (fun p => p.1 ^ 3 + p.2 ^ 3)




open scoped Classical in
/-- The counting function of the sums of three cubes: the number of `n` with `0 ≤ n ≤ N`
that are sums of three integer cubes. -/
noncomputable def repCount (N : ℕ) : ℕ :=
  (Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ)) (Finset.range (N + 1))).card





/-! ### Four rational cubes always suffice -/



end ThreeCubes


