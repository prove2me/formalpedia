-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SlackAttainment
-- name    : CRCD_QuantumChannelContinuity_SlackAttainment
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:32:35.328983+00:00
-- url     : https://prove2.me/theorems/151ec442-a913-4705-9222-d00f0a70b7a1
-- title:
--   Exact complete-positive slack attainment for channel testing
-- statement:
--   For CPTP maps $N,M:A\to B$ on nonzero finite-dimensional complex Hilbert spaces and every real $\gamma\ge0$, there exists a completely positive map $Q$ such that
--
--   $$
--   N\preceq_{\mathrm{CP}}\gamma M+Q,\qquad \operatorname{Re}\operatorname{Tr}(Q(|a\rangle\langle a|))\le\delta_\gamma(N,M)\|a\|^2\quad(a\in A).
--   $$
--
--   Here $\delta_\gamma(N,M)$ is the actual stabilized channel hockey-stick optimum. Thus the proposition $\mathrm{HockeySlackAttainment}(\gamma,N,M)$ holds for every nonnegative threshold, and in particular for the separately stated range $\gamma\ge1$. These attainment results assert existence of the slack itself; no attainment record is assumed in their premises.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SlackAttainment.lean#L32-L76

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
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sequences
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPPartialTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTester
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTraceBound
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
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
# Exact hockey-stick CP slack attainment

The closed semidefinite cone separates any infeasible target by an actual
positive Choi tester. Every such tester is bounded by the stabilized channel
hockey-stick divergence, which rules out separation at that exact value.
The Choi isomorphism then gives an attaining CP slack map. No optimization,
Slater, support, or attainability premise is used.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The exact CP-slack optimum is attained for every nonnegative threshold.
This is the previously missing Gour equation (44), stated directly in terms
of actual maps and the project's stabilized variational divergence. -/
theorem hockeySlackAttainment_of_nonneg (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ) :
    HockeySlackAttainment γ N M := by
  classical
  let b := (stdOrthonormalBasis ℂ A).toBasis
  have hN : 0 ≤ choi b N.toLinearMap := cp_to_choi b _ ⟨N.toCompletelyPositiveMap,rfl⟩
  have hM : 0 ≤ (γ : ℂ) • choi b M.toLinearMap :=
    smul_nonneg (by exact_mod_cast hγ : (0 : ℂ) ≤ (γ : ℂ))
      (cp_to_choi b _ ⟨M.toCompletelyPositiveMap,rfl⟩)
  let D : Hermitian (B ⊗[ℂ] A) :=
    ⟨choi b N.toLinearMap - (γ : ℂ) • choi b M.toLinearMap,
      hN.isSelfAdjoint.sub hM.isSelfAdjoint⟩
  let ε := channelHockey γ N M
  have hprimal : ∃ Q : Hermitian (B ⊗[ℂ] A), 0 ≤ Q ∧ D ≤ Q ∧
      hermitianLeftTrace (A := A) (B := B) Q ≤ ε • (1 : Hermitian A) := by
    by_contra hno
    obtain ⟨W,Y,hW,hY,hle,hviol⟩ := choiSlack_separation D ε hno
    have htest := choi_test_le_hockey N M hγ (W : L (B ⊗[ℂ] A)) (Y : L A) hW hY hle
    exact (not_lt_of_ge htest) hviol
  obtain ⟨Q,hQ,hDQ,hτQ⟩ := hprimal
  obtain ⟨Φ,hΦ⟩ := choiLinear_surjective (B := B) b (Q : L (B ⊗[ℂ] A))
  have hΦchoi : choi b Φ = (Q : L (B ⊗[ℂ] A)) := hΦ
  have hΦcp : IsCompletelyPositive Φ := by
    apply choi_to_cp b
    change 0 ≤ choi b Φ
    rw [hΦchoi]
    exact hQ
  refine ⟨Φ,hΦcp,?_,?_⟩
  · apply (cpLe_iff_choi_le b _ _).mpr
    change choi b N.toLinearMap ≤ choiLinear b ((γ : ℂ) • M.toLinearMap + Φ)
    rw [map_add,map_smul,choiLinear_apply,choiLinear_apply,hΦchoi]
    exact (sub_le_iff_le_add').mp hDQ
  · intro a
    apply trace_le_of_choi_marginal Φ ε _ a
    rw [show (stdOrthonormalBasis ℂ A).toBasis = b from rfl,hΦchoi]
    change leftPartialTrace (Q : L (B ⊗[ℂ] A)) ≤ (ε : ℂ) • (1 : L A)
    change leftPartialTrace (Q : L (B ⊗[ℂ] A)) ≤ ε • (1 : L A) at hτQ
    simpa only [← algebraMap_smul ℂ ε (1 : L A)] using hτQ

/-- In particular, the exact slack exists on the manuscript's range γ ≥ 1. -/
theorem hockeySlackAttainment_of_one_le (N M : CPTP A B) {γ : ℝ} (hγ : 1 ≤ γ) :
    HockeySlackAttainment γ N M :=
  hockeySlackAttainment_of_nonneg N M (zero_le_one.trans hγ)



end QuantumChannelContinuity


