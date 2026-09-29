-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:17.256379+00:00
-- url     : https://prove2.me/submissions/41ff04d8-fa00-449d-a8c7-97426c649ae7

-- Sol generated from Shared/ChebotarevGeodesicTransfer.lean
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




open ChebotarevGeodesic in
theorem solution{piS pit li : ℝ → ℝ} {d θ β c : ℝ} (hc : 0 < c) (hθβ : θ < β)
    (hli : ∀ᶠ x in atTop, c * x ^ β ≤ li x)
    (hS : HasErrorExponent piS (fun x => d * li x) θ)
    (htot : HasErrorExponent pit li θ) :
    HasErrorExponent (fun x => piS x / pit x) (fun _ => d) (θ - β) := by
  intro ε hε
  set ε₀ := min ε ((β - θ) / 2) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε (by linarith)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  have hlt : θ + ε₀ < β := by
    have h := min_le_right ε ((β - θ) / 2)
    rw [← hε₀def] at h
    linarith
  obtain ⟨C₁, hC₁, X₁, hX₁, hb₁⟩ := hS ε₀ hε₀
  obtain ⟨C₂, hC₂, X₂, hX₂, hb₂⟩ := htot ε₀ hε₀
  have hδ : 0 < β - (θ + ε₀) := by linarith
  have hbig : Tendsto (fun x : ℝ => x ^ (-(β - (θ + ε₀)))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hδ
  have hev := hbig.eventually (gt_mem_nhds (show (0 : ℝ) < c / (2 * C₂) by positivity))
  have hden : ∀ᶠ x in atTop, c / 2 * x ^ β ≤ pit x := by
    filter_upwards [hli, hev, eventually_ge_atTop X₂, eventually_gt_atTop (0 : ℝ)]
      with x hlix hxlt hxX₂ hx0
    have hsplit : x ^ (θ + ε₀) = x ^ (-(β - (θ + ε₀))) * x ^ β := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hxβ : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hkey : C₂ * x ^ (-(β - (θ + ε₀))) ≤ c / 2 := by
      calc C₂ * x ^ (-(β - (θ + ε₀))) ≤ C₂ * (c / (2 * C₂)) :=
            mul_le_mul_of_nonneg_left hxlt.le hC₂.le
        _ = c / 2 := by field_simp
    have h1 : |pit x - li x| ≤ C₂ * x ^ (θ + ε₀) := hb₂ x hxX₂
    have h2 : li x - pit x ≤ C₂ * x ^ (θ + ε₀) := by linarith [(abs_le.mp h1).1]
    have h3 : C₂ * x ^ (θ + ε₀) ≤ c / 2 * x ^ β := by
      rw [hsplit]
      calc C₂ * (x ^ (-(β - (θ + ε₀))) * x ^ β)
          = (C₂ * x ^ (-(β - (θ + ε₀)))) * x ^ β := by ring
        _ ≤ (c / 2) * x ^ β := mul_le_mul_of_nonneg_right hkey hxβ.le
    linarith
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.mp hden
  refine ⟨2 * (C₁ + |d| * C₂) / c + 1, by positivity, max (max X₁ X₂) (max X₃ 1),
    le_max_of_le_right (le_max_right _ _), fun x hx => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxβ : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
  have hxe : (0 : ℝ) < x ^ (θ + ε₀) := Real.rpow_pos_of_pos hx0 _
  have hpi : c / 2 * x ^ β ≤ pit x := hX₃ x hxX₃
  have hpipos : 0 < pit x := lt_of_lt_of_le (by positivity) hpi
  have hnum : |piS x - d * pit x| ≤ (C₁ + |d| * C₂) * x ^ (θ + ε₀) := by
    have e : piS x - d * pit x = (piS x - d * li x) - d * (pit x - li x) := by ring
    calc |piS x - d * pit x| = |(piS x - d * li x) - d * (pit x - li x)| := by rw [e]
      _ ≤ |piS x - d * li x| + |d * (pit x - li x)| := abs_sub _ _
      _ ≤ C₁ * x ^ (θ + ε₀) + |d| * (C₂ * x ^ (θ + ε₀)) := by
          rw [abs_mul]
          exact add_le_add (hb₁ x hxX₁)
            (mul_le_mul_of_nonneg_left (hb₂ x hxX₂) (abs_nonneg d))
      _ = (C₁ + |d| * C₂) * x ^ (θ + ε₀) := by ring
  have he : piS x / pit x - d = (piS x - d * pit x) / pit x := by
    field_simp
  show |piS x / pit x - d| ≤ (2 * (C₁ + |d| * C₂) / c + 1) * x ^ (θ - β + ε)
  rw [he, abs_div, abs_of_pos hpipos]
  have hstep : |piS x - d * pit x| / pit x
      ≤ ((C₁ + |d| * C₂) * x ^ (θ + ε₀)) / (c / 2 * x ^ β) := by
    have hposden : (0 : ℝ) < c / 2 * x ^ β := by positivity
    gcongr
  have hcalc : ((C₁ + |d| * C₂) * x ^ (θ + ε₀)) / (c / 2 * x ^ β)
      = (2 * (C₁ + |d| * C₂) / c) * x ^ (θ + ε₀ - β) := by
    rw [Real.rpow_sub hx0]
    field_simp
  have hmono : x ^ (θ + ε₀ - β) ≤ x ^ (θ - β + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hcoef : (0 : ℝ) ≤ 2 * (C₁ + |d| * C₂) / c := by positivity
  have hlast : (2 * (C₁ + |d| * C₂) / c) * x ^ (θ + ε₀ - β)
      ≤ (2 * (C₁ + |d| * C₂) / c + 1) * x ^ (θ - β + ε) := by
    have hxp : (0 : ℝ) ≤ x ^ (θ - β + ε) := (Real.rpow_pos_of_pos hx0 _).le
    calc (2 * (C₁ + |d| * C₂) / c) * x ^ (θ + ε₀ - β)
        ≤ (2 * (C₁ + |d| * C₂) / c) * x ^ (θ - β + ε) :=
          mul_le_mul_of_nonneg_left hmono hcoef
      _ ≤ (2 * (C₁ + |d| * C₂) / c + 1) * x ^ (θ - β + ε) := by nlinarith
  calc |piS x - d * pit x| / pit x
      ≤ ((C₁ + |d| * C₂) * x ^ (θ + ε₀)) / (c / 2 * x ^ β) := hstep
    _ = (2 * (C₁ + |d| * C₂) / c) * x ^ (θ + ε₀ - β) := hcalc
    _ ≤ (2 * (C₁ + |d| * C₂) / c + 1) * x ^ (θ - β + ε) := hlast
