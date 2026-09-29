-- Prove2me | Theorems.Thm_ChebotarevGeodesic_chebotarev_converse
-- name    : ChebotarevGeodesic.chebotarev_converse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:20:00.27193+00:00
-- url     : https://prove2.me/theorems/accabf0a-28eb-4b7b-819f-3c265057690c
-- title:
--   C5, geometric form.
-- statement:
--   **C5, geometric form.**  If every class-counting function eventually dominates its
--   predicted main term `(|C|/|G|)Â·li`, then the prime geodesic theorem with exponent `Î¸` for the
--   total counting function already implies the full Chebotarev geodesic theorem with the same
--   exponent: the implication `prime_geodesic_of_chebotarev` can be reversed under positivity.
--
--   ```lean
--   theorem ChebotarevGeodesic.chebotarev_converse(G : Type*) [Group G] [Fintype G] [DecidableEq G]
--       [Fintype (ConjClasses G)] (piC : ConjClasses G → ℝ → ℝ) (li : ℝ → ℝ) (θ : ℝ)
--       (hnn : ∀ C, ∀ᶠ x in atTop, classDensity G C * li x ≤ piC C x)
--       (hsum : HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ)
--       (C : ConjClasses G) :
--       HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ := by sorry
--
--   /-! ## 5.  Synthesis for the setting of the paper -/
--
--
--
--   /-! ## 6.  C4: a quantitative equidistribution rate -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicTransfer.lean#L310

-- Thm stub generated from Shared/ChebotarevGeodesicTransfer.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
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

open ChebotarevGeodesic

/-! ## 0.  Robustness of the exponent predicate -/


/-! ### Eventual growth suffices for sharpness

`not_hasErrorExponent_of_growth` requires the lower bound `c x^β ≤ |π − M|` for *all* `x ≥ 1`.
Oscillation estimates only ever hold for large `x`; we upgrade the three sharpness statements
accordingly. -/





/-! ## 1.  C1: an invertible transform transports the whole exponent set -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## 2.  C2: the rank obstruction -/





/-! ## 3.  C3: powers of the logarithm do not move the optimal exponent -/



/-! ## 4.  C5: a converse Chebotarev principle -/

theorem ChebotarevGeodesic.chebotarev_converse(G : Type*) [Group G] [Fintype G] [DecidableEq G]
    [Fintype (ConjClasses G)] (piC : ConjClasses G → ℝ → ℝ) (li : ℝ → ℝ) (θ : ℝ)
    (hnn : ∀ C, ∀ᶠ x in atTop, classDensity G C * li x ≤ piC C x)
    (hsum : HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ)
    (C : ConjClasses G) :
    HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ := by sorry
