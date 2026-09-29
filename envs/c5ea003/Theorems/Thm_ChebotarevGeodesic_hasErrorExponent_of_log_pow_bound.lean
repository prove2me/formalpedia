-- Prove2me | Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_of_log_pow_bound
-- name    : ChebotarevGeodesic.hasErrorExponent_of_log_pow_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:21:33.965429+00:00
-- url     : https://prove2.me/theorems/c70e91bb-f4ed-4a4c-a16f-ec67f0f7a7a9
-- title:
--   Log-absorption.
-- statement:
--   **Log-absorption.**  An error bound `K x^Î¸ (log x)^k`, the typical output of a trace
--   formula computation, yields the clean error exponent `Î¸`.
--
--   ```lean
--   theorem ChebotarevGeodesic.hasErrorExponent_of_log_pow_bound{π M : ℝ → ℝ} {θ K : ℝ} {k : ℕ} (hK : 0 ≤ K)
--       (hb : ∀ x ≥ (1 : ℝ), |π x - M x| ≤ K * x ^ θ * (Real.log x) ^ k) :
--       HasErrorExponent π M θ := by sorry
--   /-! ## Little-o characterisation -/
--
--
--
--
--   /-! ## A concrete character-table instance of the reduction -/
--
--
--   /-! ## Sharpness: the exponent is a genuine restriction -/
--
--
--
--   /-! ## Abelian Galois groups: equidistribution among `|G|` classes -/
--
--
--   variable (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicSharpness.lean#L70

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

theorem ChebotarevGeodesic.hasErrorExponent_of_log_pow_bound{π M : ℝ → ℝ} {θ K : ℝ} {k : ℕ} (hK : 0 ≤ K)
    (hb : ∀ x ≥ (1 : ℝ), |π x - M x| ≤ K * x ^ θ * (Real.log x) ^ k) :
    HasErrorExponent π M θ := by sorry
