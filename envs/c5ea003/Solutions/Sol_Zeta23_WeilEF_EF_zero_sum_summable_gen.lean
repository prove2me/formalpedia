-- Prove2me | solution 1 for Zeta23.WeilEF.EF_zero_sum_summable_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:43:43.1144+00:00
-- url     : https://prove2.me/submissions/6773730b-8ff9-4359-9d05-6375bd68fd67

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_WeilEF_ZeroSummability
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_Zeta23_WeilEF_zero_sum_inv_sq_gen
import Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le

-- from Zeta23.Poisson.PaperFT
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/


/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/









/-- [eq:hfbound] in the paper's form for `z ≠ 0`: `‖h_f(z)‖ ≤ e^{|Im z|Λ} ‖f''‖₁ / ‖z‖²`. -/
theorem norm_paperFT_le_div {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖) / ‖z‖ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact norm_paperFT_mul_sq_le hf hsupp z

end Zeta23
end

-- from Zeta23.WeilEF.ZeroSummability
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter MeasureTheory

/-! ### γ_ρ bookkeeping -/

lemma gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by
  simp [gammaOf, Complex.div_I]

lemma gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by
  simp [gammaOf, Complex.div_I]

lemma abs_im_le_norm_gammaOf (ρ : ℂ) : |ρ.im| ≤ ‖gammaOf ρ‖ := by
  rw [← gammaOf_re]; exact Complex.abs_re_le_norm _


/-- For a point of the closed strip, |Im γ_ρ| ≤ 1/2. -/
lemma abs_gammaOf_im_le {ρ : ℂ} (h : 0 ≤ ρ.re ∧ ρ.re ≤ 1) : |(gammaOf ρ).im| ≤ 1 / 2 := by
  rw [gammaOf_im, abs_le]; constructor <;> linarith [h.1, h.2]

/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/




/-! ### zero_sum_inv_sq -/





/-! ### The generic theorems (any ZeroConfig with the local count) -/




/-! ### The ζ instances -/


/-! ### EF_zero_sum_summable -/


end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Set Filter MeasureTheory

theorem solution (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
  classical
  -- support bound
  obtain ⟨r, hr⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  set Λ : ℝ := max r 0 with hΛ
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ Metric.closedBall (0:ℝ) r := hr (subset_tsupport _ (Function.mem_support.mpr hu))
    rw [Metric.mem_closedBall, _root_.dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set C₂ : ℝ := ∫ u, ‖deriv (deriv k) u‖ with hC₂
  have hC₂0 : 0 ≤ C₂ := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 2 * Real.exp (Λ / 2) * C₂ with hC
  -- comparison series
  have hg := (zero_sum_inv_sq_gen Z hA₀ hloc').mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  -- exceptional finite set: |Im ρ| < 1 (then possibly ‖γ_ρ‖ < 1)
  have hfin : (Z.window (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Z.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2
  -- ‖γ_ρ‖ ≥ |Im ρ| ≥ 1
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖gammaOf (ρ : ℂ)‖ := him.trans (abs_im_le_norm_gammaOf _)
  have hz0 : gammaOf (ρ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hstrip := Z.strip _ hρmem
  have himγ : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := abs_gammaOf_im_le hstrip
  have hFT := norm_paperFT_le_div hk hsupp hz0
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  -- assemble
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0:ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hkey : ‖paperFT k (gammaOf (ρ : ℂ))‖ ≤ C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    have hexp : Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) ≤ Real.exp (Λ / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hnsq : Complex.normSq (gammaOf (ρ : ℂ)) = ‖gammaOf (ρ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have h2 : 1 / ‖gammaOf (ρ : ℂ)‖ ^ 2 ≤ 2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [hnsq, div_le_iff₀ (by positivity)]
      have : 0 < 1 + ‖gammaOf (ρ:ℂ)‖ ^ 2 := by positivity
      rw [show 2 * (1 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2)) * ‖gammaOf (ρ:ℂ)‖ ^ 2
          = 2 * ‖gammaOf (ρ:ℂ)‖ ^ 2 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2) by ring, le_div_iff₀ this]
      nlinarith
    calc ‖paperFT k (gammaOf (ρ : ℂ))‖
        ≤ Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ / ‖gammaOf (ρ : ℂ)‖ ^ 2 := hFT
      _ = Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ * (1 / ‖gammaOf (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ Real.exp (Λ / 2) * C₂ * (2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hexp hC₂0) h2 (by positivity) (by positivity)
      _ = C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by rw [hC]; ring
  calc (Z.mult ρ : ℝ) * ‖paperFT k (gammaOf (ρ : ℂ))‖
      ≤ (Z.mult ρ : ℝ) * (C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = C * ((Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        ring
