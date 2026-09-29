-- Prove2me | Definitions.Def_Probability_Density
-- name    : Probability_Density
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:05.811557+00:00
-- url     : https://prove2.me/theorems/0bebeb93-810a-4980-ac17-b396636f27c5
-- title:
--   Aether Catalog definitions — Probability_Density
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Density`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Density.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_Basic

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

namespace ThreeCubes

open Finset




open scoped Classical in
/-- The (conjectural) statement that the density of sums of three cubes is exactly `7/9`. -/
def DensitySevenNinths : Prop :=
  ∀ N : ℕ, (Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ)) (Finset.range (9 * N))).card = 7 * N


end ThreeCubes


