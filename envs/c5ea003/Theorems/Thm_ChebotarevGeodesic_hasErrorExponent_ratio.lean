-- Prove2me | Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_ratio
-- name    : ChebotarevGeodesic.hasErrorExponent_ratio
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:22:03.701639+00:00
-- url     : https://prove2.me/theorems/7212bce7-735f-498a-a886-81abf4517023
-- title:
--   Quantitative ratio estimate.
-- statement:
--   **Quantitative ratio estimate.**  If a partial counting function satisfies
--   `piS = dÂ·li + O(x^{Î¸+Îµ})`, the total one satisfies `pi = li + O(x^{Î¸+Îµ})`, and the main term
--   grows at least like `c x^Î²` with `Î² > Î¸`, then the *ratio* converges to the density `d` at the
--   rate `x^{Î¸âÎ²+Îµ}`.  This upgrades the qualitative limit `chebotarev_natural_density` to an
--   effective statement, and shows the only way the group enters the implied constant is through
--   the density `d`.
--
--   ```lean
--   theorem ChebotarevGeodesic.hasErrorExponent_ratio{piS pit li : ℝ → ℝ} {d θ β c : ℝ} (hc : 0 < c) (hθβ : θ < β)
--       (hli : ∀ᶠ x in atTop, c * x ^ β ≤ li x)
--       (hS : HasErrorExponent piS (fun x => d * li x) θ)
--       (htot : HasErrorExponent pit li θ) :
--       HasErrorExponent (fun x => piS x / pit x) (fun _ => d) (θ - β) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicTransfer.lean#L380

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




/-! ## 5.  Synthesis for the setting of the paper -/



/-! ## 6.  C4: a quantitative equidistribution rate -/

theorem ChebotarevGeodesic.hasErrorExponent_ratio{piS pit li : ℝ → ℝ} {d θ β c : ℝ} (hc : 0 < c) (hθβ : θ < β)
    (hli : ∀ᶠ x in atTop, c * x ^ β ≤ li x)
    (hS : HasErrorExponent piS (fun x => d * li x) θ)
    (htot : HasErrorExponent pit li θ) :
    HasErrorExponent (fun x => piS x / pit x) (fun _ => d) (θ - β) := by sorry
