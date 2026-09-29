-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_three_isogeny_diagonal_card_le_four
-- name    : Cryptography.IsogenySIDH.three_isogeny_diagonal_card_le_four
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:16.931117+00:00
-- url     : https://prove2.me/theorems/5fed58c4-bcbb-419e-a359-6ed2322eddb6
-- title:
--   At most four fixed `j`-invariants, over any field.
-- statement:
--   **At most four fixed `j`-invariants, over any field.**  Even in
--   characteristics where the four CM values collide or where extra roots could a
--   priori appear, the diagonal of `Φ₃` is a nonzero polynomial of degree six whose
--   root set has at most four distinct elements by the factorisation
--   `modPoly3_diagonal_factor`.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.three_isogeny_diagonal_card_le_four[DecidableEq K] (S : Finset K) (hS : ∀ j ∈ S, modPoly3 j j = 0) : S.card ≤ 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean#L126

-- Thm stub generated from Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean
import Mathlib
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

theorem Cryptography.IsogenySIDH.three_isogeny_diagonal_card_le_four[DecidableEq K] (S : Finset K) (hS : ∀ j ∈ S, modPoly3 j j = 0) : S.card ≤ 4 := by sorry
