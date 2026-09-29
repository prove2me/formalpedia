-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyNonBacktracking
-- name    : Cryptography_IsogenySIDH_ThreeIsogenyNonBacktracking
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:18:53.36227+00:00
-- url     : https://prove2.me/theorems/2cd36005-a5d8-4c99-88da-d4b96fbe8dd2
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_ThreeIsogenyNonBacktracking
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.ThreeIsogenyNonBacktracking`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/ThreeIsogenyNonBacktracking.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
/-
# Non-backtracking and the radical obstruction for Montgomery 3-isogenies

`ThreeIsogenyMontgomery` uniformised the Montgomery 3-isogeny by the kernel
abscissa `r`: the source is `mont3Source r`, the target is `mont3Target r`, and
the two `j`-invariants are a zero of `Φ₃`.  To *iterate* the construction one
must choose a point of order three on the target, i.e. a root of
`threeDivPoly (mont3Target r) X`.  This file analyses that quartic completely.

* `threeDual_kernel` — `X = -1/(3r)` is always a root: it is the kernel of the
  dual isogeny, so this is the backtracking choice.  (This is the `ℓ = 3`
  analogue of `radTwoIso_two_torsion_image` in `RadicalWalkStructure`.)
* `threeDivPoly_target_factor` — the quartic factors *over the base field* as
  `r · threeDivPoly (mont3Target r) X = (3rX + 1) · threeNextKernelPoly r X`
  with the explicit residual cubic
  `threeNextKernelPoly r X = X³ + 3r(2 - 3r²)X² + 3r²X - r`.
  So a non-backtracking 3-step means choosing a root of that cubic.
* `threeNextKernelPoly_depressed` — the Tschirnhaus shift `X = Y - r(2 - 3r²)`
  depresses the cubic to `Y³ + 9r²(3r² - 1)(1 - r²) Y + threeDepressedConst r`.
* `three_radical_obstruction` — **a negative result.**  Away from the loci
  `r = 0`, `r² = 1` and `3r² = 1` the depressed cubic has *nonzero* linear
  coefficient, hence it is never of the form `Y³ - c`: the abscissa of the next
  kernel is *not* obtainable by extracting a single cube root in the Montgomery
  coordinate.  This is why radical 3-isogeny formulas are written in Tate normal
  form rather than in Montgomery form, and it delimits precisely how far the
  `ℓ = 2` picture (where `α² = A + 2` *is* a single square root) generalises.
  The hypothesis `3 ≠ 0` is necessary: in characteristic three the cubic
  degenerates to `X³ - r`, which is a pure cube.
* `three_radical_locus` — **and the exception.**  Exactly on the locus
  `3r² = 1` the cubic collapses to the pure cube `(X + r)³ - 4r/3`, so there the
  next kernel *is* given by one cube root.
-/

set_option maxHeartbeats 1000000

namespace Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## The dual kernel -/


/-! ## The residual cubic -/

/-- The cubic whose roots are the abscissae of the three *non-backtracking*
order-three kernels on the target curve. -/
def threeNextKernelPoly (r X : K) : K :=
  X ^ 3 + 3 * r * (2 - 3 * r ^ 2) * X ^ 2 + 3 * r ^ 2 * X - r



/-! ## Depressing the cubic -/

/-- The constant term of the depressed residual cubic. -/
def threeDepressedConst (r : K) : K :=
  2 * r ^ 3 * (2 - 3 * r ^ 2) ^ 3 - 3 * r ^ 3 * (2 - 3 * r ^ 2) - r




end Cryptography.IsogenySIDH


