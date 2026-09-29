-- Prove2me | solution 1 for ChebotarevGeodesic.not_hasErrorExponent_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:40:38.42176+00:00
-- url     : https://prove2.me/submissions/3b79c0b5-c1b7-4193-8cde-f7e923e94a19

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
theorem solution{π M : ℝ → ℝ} {θ β c : ℝ} (hc : 0 < c) (hlt : θ < β)
    (hgrow : ∀ x ≥ (1 : ℝ), c * x ^ β ≤ |π x - M x|) :
    ¬ HasErrorExponent π M θ := by
  intro h
  set ε := (β - θ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hpos : 0 < β - (θ + ε) := by rw [hεdef]; linarith
  have hbig : Tendsto (fun x : ℝ => x ^ (β - (θ + ε))) atTop atTop := tendsto_rpow_atTop hpos
  obtain ⟨x, hx1, hxX, hxbig⟩ :
      ∃ x : ℝ, 1 ≤ x ∧ X ≤ x ∧ C / c < x ^ (β - (θ + ε)) := by
    obtain ⟨x, hx⟩ := ((hbig.eventually_gt_atTop (C / c)).and
      ((eventually_ge_atTop (1:ℝ)).and (eventually_ge_atTop X))).exists
    exact ⟨x, hx.2.1, hx.2.2, hx.1⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h1 : c * x ^ β ≤ C * x ^ (θ + ε) := le_trans (hgrow x hx1) (hb x hxX)
  have hsplit : x ^ β = x ^ (β - (θ + ε)) * x ^ (θ + ε) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxe : (0 : ℝ) < x ^ (θ + ε) := Real.rpow_pos_of_pos hx0 _
  rw [hsplit] at h1
  have h2 : c * x ^ (β - (θ + ε)) ≤ C :=
    le_of_mul_le_mul_right (by rw [mul_assoc]; exact h1) hxe
  have h3 : C / c < x ^ (β - (θ + ε)) := hxbig
  rw [div_lt_iff₀ hc] at h3
  nlinarith
