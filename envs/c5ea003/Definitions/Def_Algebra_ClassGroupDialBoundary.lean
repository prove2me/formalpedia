-- Prove2me | Definitions.Def_Algebra_ClassGroupDialBoundary
-- name    : Algebra_ClassGroupDialBoundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:11:22.158549+00:00
-- url     : https://prove2.me/theorems/f0131cf3-8aa3-40e1-a280-d0d067193529
-- title:
--   Aether Catalog definitions — Algebra_ClassGroupDialBoundary
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ClassGroupDialBoundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ClassGroupDialBoundary.lean by skeleton subtraction
import Mathlib
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

namespace ClassGroupResidueDial

/-! ## 1. Discriminant `-23`: three classes, one genus -/

/-- Principal form of discriminant `-23`. -/
def ReprP23 (N : ℤ) : Prop := ∃ x y : ℤ, x ^ 2 + x * y + 6 * y ^ 2 = N

/-- Non-principal form `2x² + xy + 3y²` of discriminant `-23`. -/
def ReprQ23 (N : ℤ) : Prop := ∃ x y : ℤ, 2 * x ^ 2 + x * y + 3 * y ^ 2 = N







/-! ## 2. How much information a class-group dial can possibly carry

Even when the dial *is* readable (one class per genus), the observation is the
product `[p]·[q]` of the two factor classes.  The following counting theorem
says that this observation is exactly `|Cl|`-to-one on pairs of classes: every
observed value is compatible with `|Cl|` factorisation types, so at most
`log₂|Cl|` bits about the pair `([p],[q])` survive — and those bits are already
determined by `N mod |D|`. -/




end ClassGroupResidueDial


