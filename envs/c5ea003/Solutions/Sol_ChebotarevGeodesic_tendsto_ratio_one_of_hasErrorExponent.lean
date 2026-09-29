-- Prove2me | solution 1 for ChebotarevGeodesic.tendsto_ratio_one_of_hasErrorExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:44:09.688348+00:00
-- url     : https://prove2.me/submissions/c4e34c1e-539c-452b-9afb-66e81b4ca968

-- Sol generated from Shared/ChebotarevGeodesicDensity.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# The density statement: geodesics with Frobenius in a prescribed set of classes

Third research cycle on top of `Shared.ChebotarevGeodesic`.

The *density* form of the Chebotarev geodesic theorem asserts that the proportion of primitive
closed geodesics whose Frobenius class lies in a prescribed union `S` of conjugacy classes
tends to `∑_{C ∈ S} |C|/|G|`.  This file derives that statement from the *asymptotic* form
proved (in the paper, analytically; here, axiom-free from the framework) for each class,
under the only extra hypotheses that the main term `li` really grows like a positive power
`x^β` with `β` exceeding the error exponent — which is the case in the geodesic setting, where
`li(x) ≍ x/log x` and `θ = 25/36 < 1`.

Main results:

* `tendsto_ratio_one_of_hasErrorExponent` — an error exponent below the growth exponent of the
  main term forces `π/M → 1`;
* `chebotarev_subset` — the asymptotic for a union of classes;
* `chebotarev_natural_density` — the density statement:
  `π_S(x)/π(x) → ∑_{C ∈ S} |C|/|G|`.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## Ratio asymptotics -/


/-! ## The density statement -/


variable (G : Type*) [Group G] [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)]





open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ β c : ℝ}
    (h : HasErrorExponent π M θ) (hc : 0 < c) (hθβ : θ < β)
    (hM : ∀ᶠ x in atTop, c * x ^ β ≤ M x) :
    Tendsto (fun x => π x / M x) atTop (𝓝 1) := by
  set ε := (β - θ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hneg : 0 < β - (θ + ε) := by rw [hεdef]; linarith
  have hg : Tendsto (fun x : ℝ => (C / c) * x ^ (-(β - (θ + ε)))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-(β - (θ + ε)))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hneg
    simpa using h0.const_mul (C / c)
  have key : Tendsto (fun x => π x / M x - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hM, eventually_ge_atTop X, eventually_gt_atTop (0:ℝ)]
      with x hMx hxX hx0
    have hxβ : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hMpos : 0 < M x := lt_of_lt_of_le (by positivity) hMx
    have hb' : |π x - M x| ≤ C * x ^ (θ + ε) := hb x hxX
    have hnorm : ‖π x / M x - 1‖ = |π x - M x| / M x := by
      rw [Real.norm_eq_abs, div_sub_one (ne_of_gt hMpos), abs_div, abs_of_pos hMpos]
    rw [hnorm, div_le_iff₀ hMpos]
    have hstep : |π x - M x| ≤ C * x ^ (θ + ε) := hb'
    have hcx : C / c * x ^ (-(β - (θ + ε))) * (c * x ^ β) = C * x ^ (θ + ε) := by
      rw [show C / c * x ^ (-(β - (θ + ε))) * (c * x ^ β)
            = (C / c * c) * (x ^ (-(β - (θ + ε))) * x ^ β) by ring,
        ← Real.rpow_add hx0]
      rw [div_mul_cancel₀ C (ne_of_gt hc)]
      ring_nf
    have hmono : C / c * x ^ (-(β - (θ + ε))) * (c * x ^ β)
        ≤ C / c * x ^ (-(β - (θ + ε))) * M x := by
      refine mul_le_mul_of_nonneg_left hMx (by positivity)
    rw [hcx] at hmono
    linarith
  have := key.add_const 1
  simpa using this
