-- Prove2me | solution 1 for ChebotarevGeodesic.chebotarev_natural_density
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:46:00.580108+00:00
-- url     : https://prove2.me/submissions/dda5d18b-538e-4b21-8ad7-9dc02c019ca8

-- Sol generated from Shared/ChebotarevGeodesicDensity.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_HasErrorExponent_sum
import Theorems.Thm_ChebotarevGeodesic_prime_geodesic_of_chebotarev
import Theorems.Thm_ChebotarevGeodesic_tendsto_ratio_one_of_hasErrorExponent
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

open scoped Classical in
/-- Asymptotics for the geodesics whose Frobenius class lies in a prescribed set `S` of
conjugacy classes. -/
theorem chebotarev_subset (S : Finset (ConjClasses G)) (piC : ConjClasses G → ℝ → ℝ)
    (li : ℝ → ℝ) (θ : ℝ)
    (h : ∀ C, HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) :
    HasErrorExponent (fun x => ∑ C ∈ S, piC C x)
      (fun x => (∑ C ∈ S, classDensity G C) * li x) θ := by
  have hsum := HasErrorExponent.sum S piC (fun C x => classDensity G C * li x) θ
    (fun C _ => h C)
  have e : (fun x => ∑ C ∈ S, classDensity G C * li x)
      = fun x => (∑ C ∈ S, classDensity G C) * li x := by
    funext x
    rw [Finset.sum_mul]
  rwa [e] at hsum




open ChebotarevGeodesic in
open scoped Classical in
theorem solution(S : Finset (ConjClasses G)) (piC : ConjClasses G → ℝ → ℝ)
    (li : ℝ → ℝ) (θ β c : ℝ) (hc : 0 < c) (hθβ : θ < β)
    (hli : ∀ᶠ x in atTop, c * x ^ β ≤ li x)
    (hd : 0 < ∑ C ∈ S, classDensity G C)
    (h : ∀ C, HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) :
    Tendsto (fun x => (∑ C ∈ S, piC C x) / (∑ C : ConjClasses G, piC C x)) atTop
      (𝓝 (∑ C ∈ S, classDensity G C)) := by
  set d : ℝ := ∑ C ∈ S, classDensity G C with hddef
  -- numerator against `d * li`
  have hnum : Tendsto (fun x => (∑ C ∈ S, piC C x) / (d * li x)) atTop (𝓝 1) := by
    refine tendsto_ratio_one_of_hasErrorExponent (chebotarev_subset G S piC li θ h)
      (c := d * c) (by positivity) hθβ ?_
    filter_upwards [hli] with x hx
    have : d * (c * x ^ β) ≤ d * li x := mul_le_mul_of_nonneg_left hx hd.le
    calc d * c * x ^ β = d * (c * x ^ β) := by ring
      _ ≤ d * li x := this
  -- denominator against `li`
  have hden : Tendsto (fun x => (∑ C : ConjClasses G, piC C x) / li x) atTop (𝓝 1) :=
    tendsto_ratio_one_of_hasErrorExponent (prime_geodesic_of_chebotarev G piC li θ h) hc hθβ hli
  have hratio : Tendsto
      (fun x => d * ((∑ C ∈ S, piC C x) / (d * li x)) /
        ((∑ C : ConjClasses G, piC C x) / li x)) atTop (𝓝 (d * 1 / 1)) :=
    ((hnum.const_mul d).div hden one_ne_zero)
  have heq : ∀ᶠ x in atTop,
      d * ((∑ C ∈ S, piC C x) / (d * li x)) / ((∑ C : ConjClasses G, piC C x) / li x)
        = (∑ C ∈ S, piC C x) / (∑ C : ConjClasses G, piC C x) := by
    filter_upwards [hli, eventually_gt_atTop (0:ℝ)] with x hlix hx0
    have hxβ : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hli0 : 0 < li x := lt_of_lt_of_le (by positivity) hlix
    field_simp
  have : Tendsto (fun x => (∑ C ∈ S, piC C x) / (∑ C : ConjClasses G, piC C x)) atTop
      (𝓝 (d * 1 / 1)) := hratio.congr' heq
  simpa using this
