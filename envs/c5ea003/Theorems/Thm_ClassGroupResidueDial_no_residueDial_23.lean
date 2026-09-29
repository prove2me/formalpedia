-- Prove2me | Theorems.Thm_ClassGroupResidueDial_no_residueDial_23
-- name    : ClassGroupResidueDial.no_residueDial_23
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:29:33.568115+00:00
-- url     : https://prove2.me/theorems/f952d9cb-629b-41b2-933e-9874841271a3
-- title:
--   No residue dial at `D = -23`.
-- statement:
--   **No residue dial at `D = -23`.**  There is no modulus-`23` dial (with any
--   index type) whose classes include both forms: the mechanism that collapses
--   `D = -20` and `D = -84` genuinely fails here.
--
--   ```lean
--   theorem ClassGroupResidueDial.no_residueDial_23{ι : Type*} (d : ResidueDial 23 ι) {i j : ι}
--       (hi : d.repr i = ReprP23) (hj : d.repr j = ReprQ23) : False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ClassGroupDialBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ClassGroupDialBoundary.lean#L79

-- Thm stub generated from Algebra/ClassGroupDialBoundary.lean
import Mathlib
import Definitions.Def_Algebra_ClassGroupDialBoundary
import Definitions.Def_Algebra_ClassGroupResidueDial
/-
# Where the residue dial stops: the boundary of the `factor3` refutation

Cycle 2 of the investigation.  Cycle 1 (`Algebra.ClassGroupResidueDial`,
`Algebra.ClassGroupResidueDialD84`) proved that at `D = -20` and `D = -84` the
representation vector of the reduced binary quadratic forms is a *pure residue
dial*: the class representing `N` is a function of `N mod |D|`, so the vector is
factor-blind.

Both of those discriminants have **one class per genus**.  This file proves that
the phenomenon is *exactly* a one-class-per-genus phenomenon, by exhibiting a
discriminant where it provably fails, and it quantifies the information loss in
the cases where it holds.

## Contents

* `ClassGroupResidueDial.genus23_no_separation` : at `D = -23` (`h = 3`, a single genus) the
  principal form `x² + xy + 6y²` and the form `2x² + xy + 3y²` represent
  **exactly the same** residues mod `23` — the genus characters see nothing.
* `ClassGroupResidueDial.dial_fails_at_23` : more strongly, representability by the principal
  form is *not* a function of `N mod 23`: `59` and `13` are congruent mod `23`,
  `59 = 5² + 5·2 + 6·2²` is principal, and `13 = 2·2² + 2·1 + 3·1²` is
  represented only by the non-principal form.
* `ClassGroupResidueDial.no_residueDial_23` : consequently **no** `ResidueDial 23` can contain
  both forms — the abstract mechanism of cycle 1 breaks down at `D = -23`.
* `ClassGroupResidueDial.product_fiber_card` : in *any* finite class group the "product of the two
  factor classes" observation is exactly `|Cl|`-to-one on pairs of classes; the
  dial destroys precisely `log₂|Cl|` bits.  Instantiated for `Cl(-20) ≅ ℤ/2`
  (`fiber_card_Z2`) and `Cl(-84) ≅ (ℤ/2)²` (`fiber_card_klein`).

The upshot: the extrinsic-discriminant corner is closed *for idoneal-type
discriminants*, and the surviving frontier is discriminants with several classes
per genus, where the vector is no longer a residue dial — but where computing it
is no longer a residue computation either.
-/

open ClassGroupResidueDial

/-! ## 1. Discriminant `-23`: three classes, one genus -/

theorem ClassGroupResidueDial.no_residueDial_23{ι : Type*} (d : ResidueDial 23 ι) {i j : ι}
    (hi : d.repr i = ReprP23) (hj : d.repr j = ReprQ23) : False := by sorry
