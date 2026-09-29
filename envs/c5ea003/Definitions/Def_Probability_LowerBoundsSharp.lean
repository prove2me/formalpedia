-- Prove2me | Definitions.Def_Probability_LowerBoundsSharp
-- name    : Probability_LowerBoundsSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:26:00.471448+00:00
-- url     : https://prove2.me/theorems/ca625b14-465d-433d-95a9-0c82b723bfcf
-- title:
--   Aether Catalog definitions — Probability_LowerBoundsSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.LowerBoundsSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/LowerBoundsSharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_LowerBounds

/-!
# A sharper unconditional lower bound: `repCount N ≫ N^{19/27}`

`Probability.ThreeCubes.LowerBounds` counts the values `k³ + m³` of a *two*-parameter family
and obtains `repCount N ≫ N^{5/9} = N^{15/27}`.  The bottleneck there is that the third cube is
never used: the small cube `m³` must stay below the gap `(k+1)³ - k³ ≍ k^{2/3·3}`, so
`m ≍ k^{2/3}` and one gets `k · k^{2/3} = k^{5/3}` values below `k³`.

Here we iterate the gap trick once more.  Take

* `x ∈ [8K⁹, 16K⁹)`,
* `y ∈ [2K⁶, 4K⁶)`,
* `z ∈ [K⁴, 2K⁴)`,

so that `y³ + z³` is below the cube gap at `x` **and** `z³` is below the cube gap at `y`.  Then
the value `n = x³ + y³ + z³` determines `x = ⌊n^{1/3}⌋`, then `y = ⌊(n - x³)^{1/3}⌋`, then `z`:
the parametrisation is injective (`ThreeCubes.cube_triple_inj`).  Counting,

`16 K¹⁹` distinct sums of three cubes lie in `[0, 4168 K²⁷]`,

which is the power saving `N^{19/27} = N^{0.7037…}`, a genuine improvement on `N^{5/9}` and
now quite close to the *upper* density `7/9` of `ThreeCubes.card_isSumOfThreeCubes_le`.

The exponents produced by nesting the gap trick over `r` cubes are
`1 - (2/3)^r`: the boxes have sizes `A`, `A^{2/3}`, `A^{4/9}`, …, `A^{(2/3)^{r-1}}`, so they
contain `A^{3(1-(2/3)^r)}` triples with values up to `A³`.  For `r = 2` this is `5/9`
(the bound of `LowerBounds`) and for `r = 3` it is `19/27` — and `r = 3` is the end of the
line for *three* cubes, so `19/27` is exactly the limit of the elementary gap method here.
Going beyond it requires bounding the multiplicity of representations rather than merely
constructing injective boxes.

Main results.

* `ThreeCubes.cube_gap_decode` — the decoding step: if a remainder is below the cube gap then
  the leading cube is determined.
* `ThreeCubes.cube_triple_inj` — injectivity of `(x, y, z) ↦ x³ + y³ + z³` on the boxes above.
* `ThreeCubes.repCount_ge_nineteen` — `16 K¹⁹ ≤ repCount (4168 K²⁷)`.
* `ThreeCubes.repCount_rpow_ge` — the same in real-exponent form:
  `N^{19/27} ≤ 23 · repCount N` for `N = 4168 K²⁷`.
-/

namespace ThreeCubes

open Finset

/-! ### The decoding step -/


/-! ### The three boxes and their gap inequalities -/




/-! ### The counting -/

/-- The set of values `x³ + y³ + z³` for `x, y, z` in the three boxes. -/
def cubeTripleValues (K : ℕ) : Finset ℕ :=
  ((Finset.Ico (8 * K ^ 9) (16 * K ^ 9)) ×ˢ (Finset.Ico (2 * K ^ 6) (4 * K ^ 6)) ×ˢ
      (Finset.Ico (K ^ 4) (2 * K ^ 4))).image (fun p => p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3)







end ThreeCubes


