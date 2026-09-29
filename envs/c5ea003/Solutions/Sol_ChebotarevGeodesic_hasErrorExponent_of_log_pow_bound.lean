-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_of_log_pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:15.402888+00:00
-- url     : https://prove2.me/submissions/5e518f13-246a-4670-8c08-88a6f5546768

-- Sol generated from Shared/ChebotarevGeodesicSharpness.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_log_pow_le
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



/-! ## Abelian Galois groups: equidistribution among `|G|` classes -/


variable (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]






open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ K : ℝ} {k : ℕ} (hK : 0 ≤ K)
    (hb : ∀ x ≥ (1 : ℝ), |π x - M x| ≤ K * x ^ θ * (Real.log x) ^ k) :
    HasErrorExponent π M θ := by
  intro ε hε
  refine ⟨K * ((k + 1) / ε) ^ k + 1, by positivity, 1, le_rfl, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hlogk : (Real.log x) ^ k ≤ ((k + 1) / ε) ^ k * x ^ ε := log_pow_le hε hx
  have hsplit : x ^ (θ + ε) = x ^ θ * x ^ ε := Real.rpow_add hx0 θ ε
  have hxε : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  calc |π x - M x| ≤ K * x ^ θ * (Real.log x) ^ k := hb x hx
    _ ≤ K * x ^ θ * (((k + 1) / ε) ^ k * x ^ ε) := by
        exact mul_le_mul_of_nonneg_left hlogk (by positivity)
    _ = (K * ((k + 1) / ε) ^ k) * (x ^ θ * x ^ ε) := by ring
    _ ≤ (K * ((k + 1) / ε) ^ k + 1) * (x ^ θ * x ^ ε) := by
        have : (0 : ℝ) < x ^ θ * x ^ ε := by positivity
        nlinarith
    _ = (K * ((k + 1) / ε) ^ k + 1) * x ^ (θ + ε) := by rw [hsplit]
