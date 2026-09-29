-- Prove2me | solution 1 for ChebotarevGeodesic.tendsto_div_rpow_of_hasErrorExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:44.675304+00:00
-- url     : https://prove2.me/submissions/93dcb009-27fe-4acb-ad77-c6695ed46128

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




/-! ## Little-o characterisation -/




/-! ## A concrete character-table instance of the reduction -/


/-! ## Sharpness: the exponent is a genuine restriction -/



/-! ## Abelian Galois groups: equidistribution among `|G|` classes -/


variable (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]






open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ θ' : ℝ}
    (h : HasErrorExponent π M θ) (hlt : θ < θ') :
    Tendsto (fun x => (π x - M x) / x ^ θ') atTop (𝓝 0) := by
  set ε := (θ' - θ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hneg : θ + ε - θ' < 0 := by rw [hεdef]; linarith
  have hgoal : Tendsto (fun x : ℝ => C * x ^ (-(θ' - (θ + ε)))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-(θ' - (θ + ε)))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by rw [hεdef]; linarith)
    simpa using h0.const_mul C
  refine squeeze_zero_norm' ?_ hgoal
  filter_upwards [eventually_ge_atTop X, eventually_gt_atTop (0:ℝ)] with x hxX hx0
  have hxθ' : (0 : ℝ) < x ^ θ' := Real.rpow_pos_of_pos hx0 θ'
  have h1 : |π x - M x| ≤ C * x ^ (θ + ε) := hb x hxX
  have : ‖(π x - M x) / x ^ θ'‖ = |π x - M x| / x ^ θ' := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxθ']
  rw [this, div_le_iff₀ hxθ']
  have hmul : C * x ^ (-(θ' - (θ + ε))) * x ^ θ' = C * x ^ (θ + ε) := by
    rw [mul_assoc, ← Real.rpow_add hx0]
    ring_nf
  rw [hmul]
  exact h1
