-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_of_tendsto_div_rpow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:15.979334+00:00
-- url     : https://prove2.me/submissions/508e42fa-b1b7-455e-8c76-1cb8ee4c4604

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
theorem solution{π M : ℝ → ℝ} {θ : ℝ}
    (h : ∀ θ' > θ, Tendsto (fun x => (π x - M x) / x ^ θ') atTop (𝓝 0)) :
    HasErrorExponent π M θ := by
  intro ε hε
  have hlim := h (θ + ε) (by linarith)
  have hev : ∀ᶠ x in atTop, |π x - M x| / |x ^ (θ + ε)| < 1 := by
    have := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    simpa [Real.dist_eq, abs_div] using this
  obtain ⟨X₀, hX₀⟩ := (hev.and (eventually_gt_atTop (0:ℝ))).exists_forall_of_atTop
  refine ⟨1, one_pos, max X₀ 1, le_max_right _ _, fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨h1, hx0⟩ := hX₀ x hxX₀
  have hxpos : (0 : ℝ) < x ^ (θ + ε) := Real.rpow_pos_of_pos hx0 _
  have : |π x - M x| / x ^ (θ + ε) < 1 := by
    rwa [abs_of_pos hxpos] at h1
  rw [one_mul]
  exact le_of_lt ((div_lt_one hxpos).mp this)
