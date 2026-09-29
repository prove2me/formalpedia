-- Prove2me | Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_growth
-- name    : ChebotarevGeodesic.not_hasErrorExponent_of_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:19:26.613839+00:00
-- url     : https://prove2.me/theorems/3689fbcd-02ab-4c66-abf6-2607608eb188
-- title:
--   If the error term really is of size `x^Î²` with `Î² > Î¸`, then the exponent `Î¸` fails.
-- statement:
--   If the error term really is of size `x^Î²` with `Î² > Î¸`, then the exponent `Î¸` fails.
--   Hence `HasErrorExponent` is not vacuous, and improving the exponent is a genuine gain.
--
--   ```lean
--   theorem ChebotarevGeodesic.not_hasErrorExponent_of_growth{π M : ℝ → ℝ} {θ β c : ℝ} (hc : 0 < c) (hlt : θ < β)
--       (hgrow : ∀ x ≥ (1 : ℝ), c * x ^ β ≤ |π x - M x|) :
--       ¬ HasErrorExponent π M θ := by sorry
--
--   /-! ## Abelian Galois groups: equidistribution among `|G|` classes -/
--
--
--   variable (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicSharpness.lean#L164

-- Thm stub generated from Shared/ChebotarevGeodesicSharpness.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# Sharpness, log-absorption and abelian covers for the Chebotarev geodesic framework

This file is the *adversarial* companion to `Shared.ChebotarevGeodesic`.  Its purpose is to
show that the predicate `HasErrorExponent` is neither vacuous nor over-restrictive, and to
supply the two structural facts that make it usable in the setting of the paper
*"Chebotarev geodesic theorem: non-split case"*:

* **Log-absorption** (`hasErrorExponent_of_log_pow_bound`): a bound of the shape
  `|π x − M x| ≤ K x^θ (log x)^k`, which is what trace-formula arguments actually produce,
  implies the clean `x^{θ+ε}` statement.  The quantitative input is
  `Real.log x ≤ x^δ / δ`.
* **Little-o characterisation** (`hasErrorExponent_iff_littleO`): `HasErrorExponent π M θ`
  holds iff `(π − M)/x^{θ'} → 0` for every `θ' > θ`.  This pins the definition down and shows
  it is the standard notion.
* **Sharpness / non-vacuity** (`not_hasErrorExponent_of_growth`, `sharpness_example`): an error
  term of true size `x^β` with `β > θ` provably destroys the exponent `θ`.  In particular the
  statement "prime geodesic theorem with exponent `25/36`" is a genuine restriction: it fails
  for the (hypothetical) error term `x^{9/10}`.
* **Abelian covers** (`classDensity_of_comm`): for an abelian Galois group every conjugacy
  class is a singleton, so the Chebotarev densities are all `1/|G|` — equidistribution among
  the `|G|` classes.  Combined with `prime_geodesic_of_chebotarev` this is the classical
  "equidistribution of Frobenius" shape of the theorem.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## Log-absorption -/




/-! ## Little-o characterisation -/




/-! ## A concrete character-table instance of the reduction -/


/-! ## Sharpness: the exponent is a genuine restriction -/

theorem ChebotarevGeodesic.not_hasErrorExponent_of_growth{π M : ℝ → ℝ} {θ β c : ℝ} (hc : 0 < c) (hlt : θ < β)
    (hgrow : ∀ x ≥ (1 : ℝ), c * x ^ β ≤ |π x - M x|) :
    ¬ HasErrorExponent π M θ := by sorry
