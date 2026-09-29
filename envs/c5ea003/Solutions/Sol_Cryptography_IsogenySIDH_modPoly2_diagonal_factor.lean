-- Prove2me | solution 1 for Cryptography.IsogenySIDH.modPoly2_diagonal_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:44:31.208194+00:00
-- url     : https://prove2.me/submissions/1eedbd2a-7ec1-4629-8379-f35b46d486af

-- Sol generated from Cryptography/IsogenySIDH/RadicalWalkStructure.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_SupersingularRadicalExistence
/-
# Structure of radical 2-isogeny walks

Three structural questions about a radical isogeny walk are settled here.

1. **Does the walk backtrack?**  A 2-isogeny walk is useful only if consecutive
   steps are not dual to each other.  `radTwoIso_two_torsion_image` computes the
   image of the *non-kernel* two-torsion of `E_A`: it is the point `(-α/2, 0)` of
   the target.  Backtracking would mean taking that point as the next kernel,
   whereas the radical formula always takes `(0,0)`, which by
   `radTwoIso_four_torsion` is the image of a *four*-torsion point.
   `radicalWalk_nonbacktracking` records that these two points are distinct, so a
   radical walk never immediately retraces its step.

2. **Do two steps compose?**  `radTwoIso_two_step` chains two radical steps
   through the intermediate quadratic-twist normalisation, giving the
   end-to-end correctness statement for a length-two walk (i.e. a cyclic
   4-isogeny).

3. **Can a walk stand still?**  `modPoly2_diagonal_factor` factors the diagonal
   of the modular polynomial,
   `Φ₂(j,j) = -(j-8000)(j+3375)²(j-1728)`,
   and `radical_fixed_point_classification` deduces that a radical step can
   return to the same `j`-invariant only at `j ∈ {1728, 8000, -3375}` — the
   three CM `j`-invariants of discriminants `-4`, `-8`, `-7`.  Everywhere else
   the walk genuinely moves.
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## Non-backtracking -/



/-! ## Two-step composition (cyclic 4-isogeny) -/


/-! ## Fixed points of the walk on the `j`-line -/






open Cryptography.IsogenySIDH in
theorem solution(j : K) :
    modPoly2 j j = -(j - 8000) * (j + 3375) ^ 2 * (j - 1728) := by
  simp only [modPoly2]; ring
