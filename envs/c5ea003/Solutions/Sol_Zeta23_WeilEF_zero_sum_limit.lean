-- Prove2me | solution 1 for Zeta23.WeilEF.zero_sum_limit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:21:46.146509+00:00
-- url     : https://prove2.me/submissions/1a56209e-04e0-4b84-bb06-4f9db9d23c8a

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
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
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
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
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
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
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
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
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
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
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
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Definitions.Def_Zeta23_WeilEF_ZeroSummability
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_WeilEF_EF_zero_sum_summable_gen

-- from Zeta23.Statement
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/










/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/



section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl
@[simp] lemma zetaZeros_simple : (zetaZeros hs).simple = {ρ | zeroMult ρ = 1} := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]
@[simp] lemma zetaZeros_Nd : (zetaZeros hs).Nd T₁ T₂ = Ndist T₁ T₂ := by
  simp [ZeroConfig.Nd, Ndist, zetaZeros_window]
@[simp] lemma zetaZeros_N0 : (zetaZeros hs).N0 T₁ T₂ = N0 T₁ T₂ := by
  simp [ZeroConfig.N0, N0, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0star : (zetaZeros hs).N0star T₁ T₂ = N0star T₁ T₂ := by
  simp [ZeroConfig.N0star, N0star, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0s : (zetaZeros hs).N0s T₁ T₂ = N0simple T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simple, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_Ns : (zetaZeros hs).Ns T₁ T₂ = Nsimple T₁ T₂ := by
  simp [ZeroConfig.Ns, Nsimple, zetaZeros_window]

end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/





/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/




end Zeta23
end
end

-- from Zeta23.WeilEF.ZeroSummability
section
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






/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/




/-! ### zero_sum_inv_sq -/





/-! ### The generic theorems (any ZeroConfig with the local count) -/




/-! ### The ζ instances -/


/-! ### EF_zero_sum_summable -/

/-- The EF zero-side sum converges absolutely for every k ∈ C_c²(ℝ)
(via [eq:hfbound]: ‖h(γ_ρ)‖ ≤ e^{Λ/2}‖k''‖₁/‖γ_ρ‖², |Im γ_ρ| < 1/2) — EF_lit's Summable clause. -/
theorem EF_zero_sum_summable (hs : ZetaSeam) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  exact EF_zero_sum_summable_gen (zetaZeros hs) hA₀ (fun t => by rw [zetaZeros_N]; exact hloc t) hk hkc

end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.ZeroSumLimit
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/ZeroSumLimit.lean — consumed by Zeta23/WeilEF/FullLine.lean (full_line_identity).

The zero-side limit: along heights R_j ∈ [j+7, j+8] the finite sums Σ_{|γ_ρ| < R_j} m_ρ H(ρ)
(the zero term of rectangle_identity, Zeta23/WeilEF/Contour.lean) converge to the absolutely
convergent tsum over all nontrivial zeros (EF_zero_sum_summable,
Zeta23/WeilEF/ZeroSummability.lean), since the windows {|Im ρ| < R_j} increase and exhaust the carrier.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set


end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Topology Filter Set

theorem solution (hs : ZetaSeam) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ) atTop
      (𝓝 (∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)) := by
  classical
  set g : (zetaZeros hs).carrier → ℂ := fun ρ => ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ with hg
  -- absolute convergence : Hfn k ρ = paperFT k (gammaOf ρ) definitionally
  have hsum : Summable g := EF_zero_sum_summable hs hk hkc
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  -- the finite sets, viewed in the carrier subtype
  set s : ℕ → Finset (zetaZeros hs).carrier :=
    fun j => (Z j).subtype (· ∈ (zetaZeros hs).carrier) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ s j, g x = ∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ := by
    intro j
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ (zetaZeros hs).carrier)) (fun ρ : ℂ => (zeroMult ρ : ℂ) * Hfn k ρ)
    have h2 : (Z j).filter (· ∈ (zetaZeros hs).carrier) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemZ j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
    rfl
  -- monotone and exhausting
  have hRmono : ∀ i j : ℕ, i ≤ j → R i ≤ R j := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2, (hR j).1]
  have hmono : Monotone s := by
    intro i j hij x hx
    rw [Finset.mem_subtype, hmemZ] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have := hRmono i j hij
    exact ⟨h1, by linarith, by linarith⟩
  have hexh : ∀ b : Finset (zetaZeros hs).carrier, ∃ j, b ≤ s j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : (zetaZeros hs).carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have hx0 : IsNontrivialZero (x : ℂ) := x.2
    have habs := abs_le.mp (hMle x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset (zetaZeros hs).carrier => ∑ x ∈ S, g x) atTop
      (𝓝 (∑' x, g x)) := by
    exact hsum.hasSum
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]
