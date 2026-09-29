-- Prove2me | solution 1 for ChebotarevGeodesic.log_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:50:52.253141+00:00
-- url     : https://prove2.me/submissions/b5c1c0b2-86a4-4521-b7aa-792fb89c1f4c

-- Sol generated from Shared/ChebotarevGeodesicSharpness.lean
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

/-- The elementary inequality `log x ≤ x^δ / δ` for `x > 0` and `δ > 0`, obtained from
`log t ≤ t - 1` applied to `t = x^δ`. -/
theorem log_le_rpow_div {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x ^ δ / δ := by
  have hxδ : (0 : ℝ) < x ^ δ := Real.rpow_pos_of_pos hx δ
  have h1 : Real.log (x ^ δ) ≤ x ^ δ - 1 := Real.log_le_sub_one_of_pos hxδ
  rw [Real.log_rpow hx] at h1
  rw [le_div_iff₀ hδ]
  nlinarith



/-! ## Little-o characterisation -/




/-! ## A concrete character-table instance of the reduction -/


/-! ## Sharpness: the exponent is a genuine restriction -/



/-! ## Abelian Galois groups: equidistribution among `|G|` classes -/


variable (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]






open ChebotarevGeodesic in
theorem solution{k : ℕ} {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ k ≤ ((k + 1) / ε) ^ k * x ^ ε := by
  set δ : ℝ := ε / (k + 1) with hδdef
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hstep : (Real.log x) ^ k ≤ (x ^ δ / δ) ^ k :=
    pow_le_pow_left₀ hlog (log_le_rpow_div hδ hx0) k
  have hpow : (x ^ δ / δ) ^ k = (1 / δ) ^ k * x ^ (δ * k) := by
    rw [div_pow, ← Real.rpow_natCast (x ^ δ) k, ← Real.rpow_mul hx0.le, one_div, inv_pow]
    ring
  have hle : x ^ (δ * k) ≤ x ^ ε := by
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hk1]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hcoef : (1 / δ : ℝ) = ((k : ℝ) + 1) / ε := by
    rw [hδdef]; field_simp
  calc (Real.log x) ^ k ≤ (x ^ δ / δ) ^ k := hstep
    _ = (1 / δ) ^ k * x ^ (δ * k) := hpow
    _ ≤ (1 / δ) ^ k * x ^ ε := by
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (((k : ℝ) + 1) / ε) ^ k * x ^ ε := by rw [hcoef]
