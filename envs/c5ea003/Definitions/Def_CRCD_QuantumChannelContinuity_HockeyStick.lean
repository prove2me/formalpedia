-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
-- name    : CRCD_QuantumChannelContinuity_HockeyStick
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:38:41.729728+00:00
-- url     : https://prove2.me/theorems/10bac9b3-c963-4c33-8ccc-30dba6f0d2ef
-- title:
--   Effects and stabilized hockey-stick divergence
-- statement:
--   An effect on a finite-dimensional complex Hilbert space is an operator $T$ with $0\le T\le I$. Its probability on a density state is $\operatorname{Re}\operatorname{Tr}(T\rho)$. Define the real-valued state and stabilized channel hockey-stick quantities by
--   $$
--   E_\gamma(\rho\Vert\sigma)=\sup_{0\le T\le I}\operatorname{Re}\operatorname{Tr}[T(\rho-\gamma\sigma)],\qquad E_\gamma(N\Vert M)=\sup_{\|\psi\|=1}E_\gamma((N\otimes\mathrm{id})(\psi\psi^*)\Vert(M\otimes\mathrm{id})(\psi\psi^*)).
--   $$
--   The channel supremum uses $\psi\in H\otimes H$ and a reference copy of the input space. The zero effect provides a canonical effect and establishes the nonnegative lower bound. The upper bound by one uses $\gamma\ge0$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/HockeyStick.lean#L24-L116

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_Quantum_QuantumEntropy_CFCDeriv
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Quantum effects and hockey-stick divergence

These definitions are concrete variational testing quantities. They give
the unconditional bounds used by the threshold argument, including E ≤ 1.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {H K : Type u} [Qudit H] [Qudit K]

/-- An effect representing acceptance in a two-outcome quantum test. -/
structure Effect (H : Type u) [Qudit H] where
  op : L H
  nonneg : 0 ≤ op
  le_one : op ≤ 1

instance : Inhabited (Effect H) := ⟨⟨0, le_rfl, zero_le_one⟩⟩

@[simp] theorem Effect.default_op : (default : Effect H).op = 0 := rfl

/-- The trace of a product of positive operators is nonnegative, without
assuming the product itself is positive or that the operators commute. -/
theorem trace_product_nonneg {A B : L H} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (Tr (A * B)).re := by
  have hAp := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hBp := (LinearMap.nonneg_iff_isPositive B).mp hB
  rw [show A * B = A ∘ₗ B from rfl,
    trace_comp_eq_double_sum_eigen_overlap A B hAp hBp, Complex.re_sum]
  apply Finset.sum_nonneg
  intro j hj
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  apply mul_nonneg (hBp.nonneg_eigenvalues (hn := rfl) j)
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hAp.nonneg_eigenvalues (hn := rfl) i) (Complex.normSq_nonneg _)

/-- The Born acceptance probability. -/
noncomputable def Effect.probability (T : Effect H) (ρ : DensityState H) : ℝ :=
  (Tr (T.op * ρ.op)).re

theorem Effect.probability_nonneg (T : Effect H) (ρ : DensityState H) :
    0 ≤ T.probability ρ := trace_product_nonneg T.nonneg ρ.nonneg

theorem Effect.probability_le_one (T : Effect H) (ρ : DensityState H) :
    T.probability ρ ≤ 1 := by
  have h := trace_product_nonneg (sub_nonneg.mpr T.le_one) ρ.nonneg
  simp only [sub_mul, one_mul, map_sub, ρ.trace_one, Complex.sub_re, Complex.one_re] at h
  exact sub_nonneg.mp h

/-- Variational state hockey-stick divergence. -/
noncomputable def stateHockey (γ : ℝ) (ρ σ : DensityState H) : ℝ :=
  sSup (Set.range (fun T : Effect H => T.probability ρ - γ * T.probability σ))

theorem hockey_objective_le_one {γ : ℝ} (hγ : 0 ≤ γ)
    (ρ σ : DensityState H) (T : Effect H) :
    T.probability ρ - γ * T.probability σ ≤ 1 := by
  have h := mul_nonneg hγ (T.probability_nonneg σ)
  linarith [T.probability_le_one ρ]

theorem stateHockey_le_one {γ : ℝ} (hγ : 0 ≤ γ) (ρ σ : DensityState H) :
    stateHockey γ ρ σ ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T, rfl⟩
  exact hockey_objective_le_one hγ ρ σ T

theorem stateHockey_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (ρ σ : DensityState H) :
    0 ≤ stateHockey γ ρ σ := by
  have hb : BddAbove (Set.range (fun T : Effect H =>
      T.probability ρ - γ * T.probability σ)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact hockey_objective_le_one hγ ρ σ T
  have h := le_csSup hb (Set.mem_range_self (default : Effect H))
  simpa [stateHockey, Effect.probability] using h

variable [Nontrivial H] [Nontrivial K]

/-- The manuscript's stabilized channel hockey-stick divergence. -/
noncomputable def channelHockey (γ : ℝ) (N M : CPTP H K) : ℝ :=
  sSup (Set.range (fun ψ : PureInput (H ⊗[ℂ] H) =>
    stateHockey γ (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)))



omit [Nontrivial K] in
theorem channelHockey_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (N M : CPTP H K) :
    0 ≤ channelHockey γ N M := by
  let ψ : PureInput (H ⊗[ℂ] H) := Classical.choice inferInstance
  apply (stateHockey_nonneg hγ (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density)).trans
  unfold channelHockey
  apply le_csSup (s := Set.range (fun φ : PureInput (H ⊗[ℂ] H) =>
    stateHockey γ (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)))
    _ (Set.mem_range_self ψ)
  refine ⟨1, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact stateHockey_le_one hγ _ _

end QuantumChannelContinuity


