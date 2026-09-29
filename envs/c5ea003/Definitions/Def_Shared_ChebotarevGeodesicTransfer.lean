-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesicTransfer
-- name    : Shared_ChebotarevGeodesicTransfer
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:40.592065+00:00
-- url     : https://prove2.me/theorems/60641435-627f-4e53-b795-d6690f8ad505
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesicTransfer
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesicTransfer`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesicTransfer.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
/-
# Chebotarev geodesic theorem: transfer, obstruction, and converse

A fourth research cycle built on `Shared.ChebotarevGeodesic`,
`Shared.ChebotarevGeodesicSharpness` and `Shared.ChebotarevGeodesicOptimal`.

The previous cycles produced the exponent calculus, the invertible-transform reduction
(the abstract form of the paper's reduction of the non-split case to the split case), the
structure theorem `exponentSet = Ici (optimalExponent)`, and sharpness examples.  This file
resolves, inside that framework, three of the conjectures that were left open:

* **C1 (transport of the whole exponent set).**  An invertible transform of a family of
  counting functions does not merely transfer one admissible exponent: it induces an
  *equality of joint exponent sets*, hence of joint optimal exponents
  (`jointExponentSet_transform`, `jointOptimalExponent_transform`).

* **C2 (a rank obstruction).**  The invertibility hypothesis is not an artefact of the proof.
  For a *singular* transform there are families whose transforms are exact and whose
  individual optimal exponents are arbitrarily large (`singular_transform_no_transfer`,
  `det_zero_no_transfer`), and in fact the transfer principle holds for a matrix `A`
  **iff** `det A ≠ 0` (`transfer_iff_det_ne_zero`).

* **C3 (log powers are invisible).**  `optimalExponent (M + K x^θ log^k x) M = θ` exactly
  (`optimalExponent_log_pow`): the `ε` in "`25/36 + ε`" hides log powers and nothing more.

* **C5 (a converse Chebotarev principle).**  If the class-counting functions dominate their
  main terms then the single aggregate estimate implies all the individual ones
  (`hasErrorExponent_of_nonneg_summands`, `chebotarev_converse`), and the positivity
  hypothesis cannot be dropped (`cancellation_counterexample`).

Supporting the above, the sharpness machinery of cycle 3 is upgraded from "growth for all
`x ≥ 1`" to "growth eventually", which is what genuine oscillation estimates provide.
-/


open Finset Filter Set
open scoped Topology

namespace ChebotarevGeodesic

/-! ## 0.  Robustness of the exponent predicate -/


/-! ### Eventual growth suffices for sharpness

`not_hasErrorExponent_of_growth` requires the lower bound `c x^β ≤ |π − M|` for *all* `x ≥ 1`.
Oscillation estimates only ever hold for large `x`; we upgrade the three sharpness statements
accordingly. -/





/-! ## 1.  C1: an invertible transform transports the whole exponent set -/

section Transform

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear transform of a family of counting functions by a matrix (a "character
table"): `(A · f) j (x) = ∑ i A j i · f i (x)`. -/
def transform (A : Matrix ι ι ℝ) (f : ι → ℝ → ℝ) (j : ι) : ℝ → ℝ :=
  fun x => ∑ i, A j i * f i x



/-- The set of exponents admissible for *every* member of a family. -/
def jointExponentSet (f M : ι → ℝ → ℝ) : Set ℝ := {θ | ∀ i, HasErrorExponent (f i) (M i) θ}




/-- The infimal exponent valid for the whole family. -/
noncomputable def jointOptimalExponent (f M : ι → ℝ → ℝ) : ℝ := sInf (jointExponentSet f M)


/-! ## 2.  C2: the rank obstruction -/




end Transform

/-! ## 3.  C3: powers of the logarithm do not move the optimal exponent -/



/-! ## 4.  C5: a converse Chebotarev principle -/




/-! ## 5.  Synthesis for the setting of the paper -/



/-! ## 6.  C4: a quantitative equidistribution rate -/



end ChebotarevGeodesic


