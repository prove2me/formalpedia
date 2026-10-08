-- Prove2me | solution 1 for QuantumChannelContinuity.theorem_one_of_regularizedRelative_top
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:09:36.013109+00:00
-- url     : https://prove2.me/submissions/ec31fa27-bba0-4afd-b7fe-2dee80e19b2e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Inv
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelDominationBounds
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelProducts
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
import Definitions.Def_CRCD_QuantumChannelContinuity_ConcreteMain
import Definitions.Def_CRCD_QuantumChannelContinuity_DilationExistence
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_FiniteInfinite
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_PowerRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_QuantumMain
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationIdentities
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationSup
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizedExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateDominationBounds
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceFilter
import Definitions.Def_CRCD_QuantumChannelContinuity_TracePowerBounds

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Concrete stabilized divergences and hockey-stick testing

Reference systems, pure inputs, channel outputs, and tests are actual
finite-dimensional quantum objects from Lean-Quantum. The reference is a
second copy of the input space, as in the manuscript.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

universe u

variable {H K : Type u} [Qudit H] [Qudit K]















variable [Nontrivial H] [Nontrivial K]















/-- The same concrete input gives infinity for every order above one. -/
private theorem channelRenyi_top_of_support_mismatch (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H)) {α : ℝ} (hα : 1 < α)
    (hs : ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op) :
    channelRenyi α N M = ⊤ := by
  apply top_unique
  have h := stateRenyi_le_channel N M α ψ
  simpa [stateRenyi_eq_top_of_not_support hα _ _ hs] using h

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-! # Canonical regrouping of concrete channel tensor powers -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false



variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]











/-- Block length one equals the original stabilized channel divergence. -/
private theorem blockRenyi_one {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP A B) :
    blockRenyi p N M 1 = channelRenyi p N M :=
  channelRenyi_isometry hp hp1 (powerOneIso A) (powerOneIso B)
    (channelPower N 1) (channelPower M 1) N M
    (channelPower_one_intertwine N) (channelPower_one_intertwine M)



end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Superadditivity and exact block scaling of concrete regularization

The identities concern the actual tensor powers and the actual stabilized
channel divergences. Their proof uses product inputs, canonical Hilbert-space
regrouping, and the extended-real supremum argument.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]









private theorem channelRenyi_le_regularized {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) : channelRenyi p N M ≤ regularizedRenyi p N M := by
  have h := blockRenyi_le_regularized p N M (n := 1) zero_lt_one
  simpa only [blockRenyi_one hp hp1, Nat.cast_one, mul_one] using h



end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Complete finite/infinite classification and pointwise limits

The support dichotomy is connected to the actual block-supremum divergences.
Finiteness is equivalent to finite CP domination; infinite relative entropy
has a concrete one-use Choi witness and satisfies the whole continuity claim.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]







/-- Infinite regularized relative entropy has a genuine single-use support witness. -/
private theorem channel_support_mismatch_of_regularizedRelative_top (N M : CPTP H K)
    (htop : regularizedRelative N M = ⊤) :
    ∃ ψ : PureInput (H ⊗[ℂ] H),
      ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op := by
  rcases cp_domination_or_support_mismatch N M with ⟨c, hc, hdom⟩ | hψ
  · exact ((regularized_finite_of_cp_domination N M hc hdom).1 htop).elim
  · exact hψ

end QuantumChannelContinuity

open QuantumChannelContinuity
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
open QuantumChannelContinuity in
/-- The full two-sided continuity conclusion whenever regularized relative
entropy is infinite. No witness, monotonicity, or filter premise is supplied. -/
theorem solution (N M : CPTP H K)
    (htop : regularizedRelative N M = ⊤) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  obtain ⟨ψ, hs⟩ := channel_support_mismatch_of_regularizedRelative_top N M htop
  rw [htop, ← nhdsLT_sup_nhdsGT]
  apply Filter.Tendsto.sup
  · have hleft := stateRenyi_tendsto_top_left_of_not_support _ _ hs
    have he : Tendsto (fun α =>
        (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal)
        (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
      simpa only [EReal.toENNReal_top] using
        (EReal.continuous_toENNReal.tendsto ⊤).comp hleft
    apply tendsto_nhds_top_mono he
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)).filter_mono nhdsWithin_le_nhds]
      with α hα hαhalf
    exact (stateRenyi_le_channel N M α ψ).trans
      (channelRenyi_le_regularized hαhalf.le (ne_of_lt hα) N M)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    apply Eq.symm
    apply top_unique
    simpa only [channelRenyi_top_of_support_mismatch N M ψ hα hs] using
      channelRenyi_le_regularized (by have hα' : 1 < α := hα; linarith) (ne_of_gt hα) N M

end
