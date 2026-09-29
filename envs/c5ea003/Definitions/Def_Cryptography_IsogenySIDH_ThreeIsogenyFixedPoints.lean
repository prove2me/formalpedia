-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyFixedPoints
-- name    : Cryptography_IsogenySIDH_ThreeIsogenyFixedPoints
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:08.237167+00:00
-- url     : https://prove2.me/theorems/ce16a296-2c7f-4737-966b-261a64c53f30
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_ThreeIsogenyFixedPoints
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.ThreeIsogenyFixedPoints`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
/-
# Fixed points of a 3-isogeny step on the `j`-line

`RadicalWalkStructure.lean` classified the `j`-invariants that a *2*-isogeny
step can fix, by factoring the diagonal of the level-2 modular polynomial:
`Φ₂(j,j) = -(j-8000)(j+3375)²(j-1728)`.  The level-3 side, developed in
`ThreeIsogenyMontgomery.lean`, supplied the explicit Costello–Hisil 3-isogeny
and the certificate `Φ₃(j(E_A), j(E_{A'})) = 0`, but left the corresponding
question open:

> can a 3-isogeny step of the Montgomery family return to the same
> `j`-invariant?

This file answers it completely.

* `modPoly3_diagonal_factor` — the diagonal of `Φ₃` factors as
  `Φ₃(j,j) = -j (j-8000)² (j-54000) (j+32768)²`,
  a polynomial identity of degree six.  The four roots are exactly the CM
  `j`-invariants of discriminants `-3`, `-8`, `-12` and `-11`, i.e. the
  `j`-invariants of the curves carrying an endomorphism of norm three.
* `three_isogeny_fixed_point_classification` — consequently a 3-isogeny step can
  fix a `j`-invariant only at `j ∈ {0, 8000, 54000, -32768}`.
* `modPoly3_diagonal_roots` — all four values really are zeroes of `Φ₃(j,j)`, so
  the list cannot be shortened on the level of the modular polynomial.
* `three_isogeny_step_moves` — the geometric consequence for the Montgomery
  family: away from those four values, the Costello–Hisil 3-isogeny genuinely
  changes the `j`-invariant.
* `three_isogeny_diagonal_card_le_four` — over any field at most four
  `j`-invariants can be fixed.

Together with `RadicalNonBacktracking.lean` and
`BacktrackingCharacteristic.lean` this completes the picture of *stationary*
behaviour for both levels handled in this thread: level 2 fixes at most the
three CM values `{1728, 8000, -3375}`, level 3 at most the four CM values
`{0, 8000, 54000, -32768}`, and the only value common to both lists is `8000`
(discriminant `-8`).
-/

set_option maxHeartbeats 1000000

namespace Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The diagonal of the level-three modular polynomial -/



/-! ## Classification of the fixed `j`-invariants -/



/-! ## A counting bound for the diagonal -/

/-- The diagonal of `Φ₃` as an honest univariate polynomial of degree six. -/
noncomputable def modPoly3Diag : K[X] :=
  C (-1) * X ^ 6 + C 4464 * X ^ 5 + C 2585778176 * X ^ 4 + C 17800519680000 * X ^ 3
    + C (-769939996672000000) * X ^ 2 + C 3710851743744000000000 * X





/-! ## Comparison of the two levels -/


end Cryptography.IsogenySIDH


