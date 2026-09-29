-- Prove2me | solution 1 for Zeta23.WeilEF.zero_sum_inv_sq_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:41:04.717585+00:00
-- url     : https://prove2.me/submissions/ba0551ed-3677-431c-a099-a76c8f0dc80c

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
import Theorems.Thm_Zeta23_Tail_LocalCount_ofWindowCount
import Theorems.Thm_Zeta23_WeilEF_weight_le

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





/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/


lemma summable_weight :
    Summable (fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1:ℝ) < 3/2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact weight_le n hn


/-! ### zero_sum_inv_sq -/


lemma key_lt (y : ℝ) : (key y : ℝ) < y := by
  have := Int.ceil_lt_add_one y; unfold key; push_cast; linarith

lemma le_key_add_one (y : ℝ) : y ≤ (key y : ℝ) + 1 := by
  have := Int.le_ceil y; unfold key; push_cast; linarith

/-- if n < y ≤ n+1 then 1 + y² ≥ (1 + n²)/4. -/
lemma one_add_sq_ge {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]

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
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc'
  have hW := summable_weight
  refine summable_of_sum_le (c := 4 * A₀ * totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])) fun s => ?_
  -- group by the window key of Im ρ
  set κ : Z.carrier → ℤ := fun ρ => key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨key_lt _, le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact le_key_add_one _
      have hge := one_add_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, gammaOf_re]; nlinarith [sq_nonneg ((gammaOf (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          = (Z.mult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
        _ ≤ (Z.mult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
    calc ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
      ≤ ∑ n ∈ s.image κ, 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
