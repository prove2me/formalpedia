-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_two_and_three_fixed_point_meet
-- name    : Cryptography.IsogenySIDH.two_and_three_fixed_point_meet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:18.168493+00:00
-- url     : https://prove2.me/theorems/fed58d6d-db57-4458-bbf6-09f825bdfbf8
-- title:
--   The two stationary sets meet only at `j = 8000`.
-- statement:
--   **The two stationary sets meet only at `j = 8000`.**  In characteristic zero
--   a `j`-invariant fixed by both a 2-isogeny step and a 3-isogeny step must be
--   `8000`, the CM `j`-invariant of discriminant `-8` — the unique discriminant in
--   this thread whose order contains an endomorphism of norm two *and* one of norm
--   three.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.two_and_three_fixed_point_meet[CharZero K] {j : K}
--       (hj2 : modPoly2 j j = 0) (hj3 : modPoly3 j j = 0) : j = 8000 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean#L146

-- Thm stub generated from Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyFixedPoints
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

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The diagonal of the level-three modular polynomial -/



/-! ## Classification of the fixed `j`-invariants -/



/-! ## A counting bound for the diagonal -/






/-! ## Comparison of the two levels -/

theorem Cryptography.IsogenySIDH.two_and_three_fixed_point_meet[CharZero K] {j : K}
    (hj2 : modPoly2 j j = 0) (hj3 : modPoly3 j j = 0) : j = 8000 := by sorry
