-- Prove2me | solution 1 for Zeta23.RvM.half_count_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:43:29.098311+00:00
-- url     : https://prove2.me/submissions/33feef4e-01ec-484c-9d9a-bdc570573813

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_ZerosBound
import Theorems.Thm_Zeta23_RvM_analyticOrderNatAt_gfun
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at

-- from Zeta23.Defs.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂








end Zeta23.ZeroConfig
end
end

-- from Zeta23.RvM.ZetaGrowth
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/


/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/





theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zeta_growth_right_at⟩

/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/



/-- Lower bound at the Jensen disc centre: 0 < 2 − π²/6 ≤ ‖ζ(s)‖ for Re s ≥ 2. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith


/-- 1/3 < 2 − π²/6 (π < 3.15 ⇒ π²/6 < 1.654). -/
lemma one_third_lt_two_sub_pi_sq_div_six : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Consumer interface.** ‖ζ(2 + it)‖ ≥ 1/3 for all real t. -/
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six]



end RvM
end Zeta23
end
end

-- from Zeta23.RvM.LocalCount
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM

/-- zeros of ζ in any compact set are finite (none accumulate, none near the pole). -/
theorem riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ⟩


lemma comp_affine_analyticAt {s₀ c z : ℂ} (h : s₀ + c * z ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (s₀ + c * z)) z := by
  have hζ : AnalyticAt ℂ riemannZeta (s₀ + c * z) := riemannZeta_analyticOnNhd_compl_one _ h
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hζ.comp_of_eq haff rfl

lemma gfun_analyticAt {s₀ c u z : ℂ} (h : s₀ + c * z ≠ 1) : AnalyticAt ℂ (gfun s₀ c u) z := by
  have h1 := comp_affine_analyticAt h
  have h2 : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  have := h1.mul h2
  exact this










end Zeta23.RvM
end
open Complex Set Filter Topology Metric
open Zeta23
open Zeta23.RvM

theorem solution :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨A, C, hC, hgrowth⟩ := zeta_growth_right
  have hL := zeta_lower_bound_two
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  -- constants
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A'), fun t ht => ?_⟩
  -- centre and rescaling
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hζc₀ : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have hζc₀ne : riemannZeta c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζc₀; norm_num at hζc₀
  set u : ℂ := (riemannZeta c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hζc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := gfun c₀ κ u with hg
  -- geometry: ‖c₀ + κ z - 1‖ ≥ |t + 1/2| - 1.9 ‖z‖
  have hc₀1 : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have : (c₀ - 1).im = t + 1/2 := by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist : ∀ z : ℂ, ‖z‖ ≤ 1 → |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    intro z hz
    have h1 : ‖c₀ - 1‖ - ‖κ * z‖ ≤ ‖c₀ + κ * z - 1‖ := by
      have := norm_sub_norm_le (c₀ - 1) (-(κ * z))
      rw [norm_neg] at this
      have e : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
      rw [e] at this; linarith
    rw [norm_mul, hnormκ] at h1; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + κ * z ≠ 1 := by
    intro z hz h
    have := hdist z hz
    rw [h, sub_self, norm_zero] at this
    nlinarith
  -- hypotheses of ZerosBound
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, _root_.dist_zero_right] at hz
    exact gfun_analyticAt (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [hg, gfun, hu, hζc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]; nlinarith [norm_nonneg z]
    · simpa [hg, gfun, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [hR])
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1, -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by have := hdist z hz1; rw [hR] at hz; nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1 : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre hs1
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) hsim hA'0
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [hg, gfun, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  -- the window's β ≥ 1/2 part maps injectively into the zero finset of g
  set W : Set ℂ := zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := (zetaZeroConfig.window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : IsNontrivialZero ρ := hρZ
    refine ⟨?_, ?_⟩
    · -- ‖φ ρ‖ ≤ 0.84
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gfun, hφinv]; rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    have hρ : IsNontrivialZero ρ := hρZ
    rw [analyticOrderNatAt_gfun hκ0 hu0 (by rw [hφinv]; exact hρ.not_trivial.2), hφinv]
  -- compare the sums
  have hsum : NhalfR t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfR
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  -- log B ≤ (|log 3C| + 2A') log(|t|+3)
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc NhalfR t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring
