-- Prove2me | solution 1 for QuantumChannelContinuity.regularizedRenyi_tendsto_one_left_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:07:54.517988+00:00
-- url     : https://prove2.me/submissions/cf8c2ad7-d66d-45ca-b6bb-039604ba2d6a

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
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ENNReal.Inv
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
import Mathlib.Topology.Sequences
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ContinuityAssembly
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
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPPartialTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackAttainment
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTester
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTraceBound
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






/-! # Order-one limits on the full finite support domain -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set MeasureTheory
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false







universe u
variable {H : Type u} [Qudit H] [Nontrivial H]




































/-- The state limit needed by the optimization over every block and input,
with no faithfulness, support, or commutativity hypothesis. -/
private theorem stateRenyi_tendsto_one_left {H : Type} [Qudit H] [Nontrivial H] (ρ σ : DensityState H) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[<] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) :=
  (stateRenyi_tendsto_one ρ σ).mono_left (nhdsWithin_mono _ (fun _ h => ne_of_lt h))

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

/-- Every concrete normalized block output has the required left limit. -/
private theorem inputRenyi_tendsto_one_left (N M : CPTP H K) (i : BlockInput H) :
    Tendsto (fun α => inputRenyi N M α i) (𝓝[<] (1 : ℝ))
      (𝓝 (inputRelative N M i)) := by
  have hs := stateRenyi_tendsto_one_left
    (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)
  have he := (EReal.continuous_toENNReal.tendsto _).comp hs
  exact ENNReal.Tendsto.div_const he
    (Or.inr (by exact_mod_cast i.1.property.ne'))









end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Assembly from order monotonicity

This intermediate module isolates order monotonicity as the final state-level
input. All state limits, support cases, CP caps, exact slack attainment, and
regularization identities are supplied by the preceding concrete proofs.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]









end QuantumChannelContinuity

open QuantumChannelContinuity
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
open QuantumChannelContinuity in
/-- The open interval suffices for the left limit, avoiding any need to
include the endpoint α = 1/2 in the order-monotonicity statement. -/
theorem solution (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1)) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[<] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  have hle {α : ℝ} (hα : α ∈ Ioo (1 / 2) 1) (i : BlockInput H) :
      inputRenyi N M α i ≤ inputRelative N M i := by
    apply ge_of_tendsto (inputRenyi_tendsto_one_left N M i)
    filter_upwards [Ioo_mem_nhdsLT hα.2] with β hβ
    exact hmono i hα ⟨hα.1.trans hβ.1, hβ.2⟩ hβ.1.le
  simp_rw [regularizedRenyi_eq_input_sup, regularizedRelative_eq_input_sup]
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp hb
    filter_upwards [(tendsto_order.mp (inputRenyi_tendsto_one_left N M i)).1 b hi]
      with α hα
    exact hα.trans_le (le_iSup (inputRenyi N M α) i)
  · intro b hb
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with α hα
    exact (iSup_le fun i => (hle hα i).trans
      (le_iSup (inputRelative N M) i)).trans_lt hb

end
