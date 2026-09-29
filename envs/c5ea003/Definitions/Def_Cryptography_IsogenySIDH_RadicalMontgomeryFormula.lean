-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
-- name    : Cryptography_IsogenySIDH_RadicalMontgomeryFormula
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:15:53.18623+00:00
-- url     : https://prove2.me/theorems/62caaaeb-5637-469d-9256-92f329ec1809
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_RadicalMontgomeryFormula
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.RadicalMontgomeryFormula`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/RadicalMontgomeryFormula.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
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

namespace Cryptography.IsogenySIDH

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## Generalized (twisted) Montgomery models -/

/-- The generalized Montgomery equation `B y² = x³ + A x² + x`.  For `B = 1`
this is `OnMontgomery A`; a non-square `B` describes the quadratic twist. -/
def genMont (B A : K) (P : K × K) : Prop :=
  B * P.2 ^ 2 = P.1 ^ 3 + A * P.1 ^ 2 + P.1




/-! ## The radical parameter formula -/

/-- **Radical 2-isogeny parameter.**  If `α² = A + 2`, the curve `2`-isogenous
to `E_A` via the kernel `⟨(0,0)⟩` has Montgomery coefficient `(A+6)/(2α)`. -/
def radTwoParam (A α : K) : K := (A + 6) / (2 * α)

/-- The twisting coefficient of the normalized model produced by the radical
step. -/
def radTwoTwist (α : K) : K := 1 / (8 * α ^ 3)

/-- **The radical 2-isogeny map** from `E_A` to the normalized quotient. -/
def radTwoIso (α : K) (P : K × K) : K × K :=
  ((P.1 - 1) ^ 2 / (2 * α * P.1), P.2 * (P.1 ^ 2 - 1) / P.1 ^ 2)



/-! ## Where the radical comes from: four-torsion -/

/-- The `x`-coordinate of the duplication map on `E_A`, in the form used by
Montgomery arithmetic. -/
def mDoubleX (A x : K) : K := (x ^ 2 - 1) ^ 2 / (4 * x * (x ^ 2 + A * x + 1))







/-! ## The image of the kernel-adjacent points -/



/-! ## Uniqueness of the Montgomery normalisation -/






/-! ## Iterating: radical isogeny walks -/

/-- The parameter sequence of a radical-isogeny walk driven by a chosen
sequence `r` of square roots. -/
def radChain (r : ℕ → K) (A : K) : ℕ → K
  | 0 => A
  | n + 1 => radTwoParam (radChain r A n) (r n)



/-- A radical walk is *admissible* when every chosen root is a nonzero square
root of `A_n + 2`. -/
def AdmissibleWalk (r : ℕ → K) (A : K) : Prop :=
  ∀ n, r n ≠ 0 ∧ (r n) ^ 2 = radChain r A n + 2




end Cryptography.IsogenySIDH


