-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_mDoubleX_eq_zero_iff
-- name    : Cryptography.IsogenySIDH.mDoubleX_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:42:58.871793+00:00
-- url     : https://prove2.me/theorems/b788d1e4-c0d0-4a03-a04a-996cb876e957
-- title:
--   Points above the kernel.
-- statement:
--   **Points above the kernel.**  An affine point of `E_A` doubles to the
--   two-torsion point `(0,0)` exactly when its abscissa is `1` or `-1`.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.mDoubleX_eq_zero_iff{A x : K}
--       (hd : 4 * x * (x ^ 2 + A * x + 1) ≠ 0) :
--       mDoubleX A x = 0 ↔ x = 1 ∨ x = -1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/RadicalMontgomeryFormula.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/RadicalMontgomeryFormula.lean#L117

-- Thm stub generated from Cryptography/IsogenySIDH/RadicalMontgomeryFormula.lean
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

theorem Cryptography.IsogenySIDH.mDoubleX_eq_zero_iff{A x : K}
    (hd : 4 * x * (x ^ 2 + A * x + 1) ≠ 0) :
    mDoubleX A x = 0 ↔ x = 1 ∨ x = -1 := by sorry
