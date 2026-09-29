-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radTwoIso_four_torsion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:49:02.432294+00:00
-- url     : https://prove2.me/submissions/b8d6cd97-8e3b-4a69-a4df-753be8ce0540

-- Sol generated from Cryptography/IsogenySIDH/RadicalMontgomeryFormula.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
/-
# The radical 2-isogeny formula on Montgomery curves

`Catalog/Cryptography/IsogenySIDH/RadicalMontgomery.lean` verified the *affine
quotient* of a Montgomery curve `E_A : y² = x³ + A x² + x` by its rational
two-torsion point `(0,0)`: the image satisfies the (non-Montgomery) equation
`Y² = X³ + A X² - 4 X - 4 A`.  That is only half of a radical-isogeny step.  The
genuinely *radical* half is the renormalisation of the image back into Montgomery
form, which requires extracting a square root.

This file supplies that missing half and therefore closes the loop:

* `genMont B A P` is the generalized (twisted) Montgomery equation
  `B y² = x³ + A x² + x`.  Allowing the twist coefficient `B` makes the
  renormalisation *rational in a single radical* `α = √(A+2)`, which is exactly
  the shape used by radical-isogeny algorithms.
* `radTwoParam A α = (A+6)/(2α)` is the **radical 2-isogeny parameter formula**.
* `radTwoIso α (x,y) = ((x-1)²/(2αx), y(x²-1)/x²)` is the associated explicit
  rational map, and `radTwoIso_mem` is its correctness theorem.
* `radical_is_four_torsion_ordinate` explains *where the radical comes from*:
  `α` is precisely the `y`-coordinate of an affine point of `E_A` lying above
  `(0,0)` under duplication, i.e. of a point of order four.  This is the
  structural reason radical isogenies avoid square-root extraction at run time.
* `mont_normalisation_unique` shows the two sign choices `±α` exhaust all
  Montgomery renormalisations, and `radTwoParam_neg` identifies the second one
  with the quadratic twist.
* `radChain` iterates the step and `radChain_mem` verifies an entire chain by
  induction, which is the algorithmic content of a radical-isogeny walk.

Everything is stated over an arbitrary field, so it applies verbatim to the
quadratic finite fields `𝔽_{p²}` on which supersingular isogeny cryptography
takes place.
-/

open Cryptography.IsogenySIDH

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## Generalized (twisted) Montgomery models -/





/-! ## The radical parameter formula -/






/-! ## Where the radical comes from: four-torsion -/








/-! ## The image of the kernel-adjacent points -/



/-! ## Uniqueness of the Montgomery normalisation -/






/-! ## Iterating: radical isogeny walks -/









open Cryptography.IsogenySIDH in
theorem solution(α : K) (y : K) :
    radTwoIso α (1, y) = (0, 0) := by
  simp [radTwoIso]
