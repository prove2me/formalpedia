-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ContinuityAssembly
-- name    : CRCD_QuantumChannelContinuity_ContinuityAssembly
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:57:26.441373+00:00
-- url     : https://prove2.me/theorems/280f7e86-461a-4fd2-81d9-eff96bc6fdec
-- title:
--   Construction of finite threshold inputs
-- statement:
--   Let $N,M$ be completely positive trace-preserving maps between nonzero finite-dimensional complex Hilbert spaces. Assume $D^{\mathrm{reg}}(N\Vert M)<+\infty$ and, for every positive block input $i$, monotonicity of the normalized input Rényi divergence in $\alpha>1$. The constructor `quantumThresholdInputs_of_mono` produces the complete finite threshold record. It obtains a completely positive domination constant and a finite cap, transfers input monotonicity to the regularized supremum, proves the relative-to-Rényi bound, and supplies block domination, hockey-stick slack attainment, and power scaling. The finiteness and input-monotonicity assumptions remain explicit arguments to this constructor.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ContinuityAssembly.lean#L25-L84

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
# Assembly from order monotonicity

This intermediate module isolates order monotonicity as the final state-level
input. All state limits, support cases, CP caps, exact slack attainment, and
regularization identities are supplied by the preceding concrete proofs.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

theorem inputRenyi_tendsto_one_right (N M : CPTP H K) (i : BlockInput H) :
    Tendsto (fun α => inputRenyi N M α i) (𝓝[>] (1 : ℝ))
      (𝓝 (inputRelative N M i)) := by
  have hs := (stateRenyi_tendsto_one
    (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).mono_left
      (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from
        fun _ hx => ne_of_gt hx))
  exact ENNReal.Tendsto.div_const
    ((EReal.continuous_toENNReal.tendsto _).comp hs)
    (Or.inr (by exact_mod_cast i.1.property.ne'))

theorem inputRelative_le_inputRenyi_of_mono (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1))
    {α : ℝ} (hα : 1 < α) (i : BlockInput H) :
    inputRelative N M i ≤ inputRenyi N M α i := by
  apply le_of_tendsto (inputRenyi_tendsto_one_right N M i)
  filter_upwards [Ioo_mem_nhdsGT hα] with β hβ
  exact hmono i hβ.1 hα hβ.2.le

theorem regularizedRelative_le_regularizedRenyi_of_mono (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1))
    {α : ℝ} (hα : 1 < α) : regularizedRelative N M ≤ regularizedRenyi α N M := by
  rw [regularizedRelative_eq_input_sup, regularizedRenyi_eq_input_sup]
  exact iSup_mono (inputRelative_le_inputRenyi_of_mono N M hmono hα)

/-- Construct every finite threshold input from finite relative entropy and
actual state-order monotonicity. All operator and regularization fields are proved. -/
noncomputable def quantumThresholdInputs_of_mono (N M : CPTP H K)
    (hfin : regularizedRelative N M ≠ ⊤)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1)) :
    QuantumThresholdInputs N M := by
  let hex := (regularizedRelative_ne_top_iff_cp_domination N M).mp hfin
  let c := Classical.choose hex
  have hc := (Classical.choose_spec hex).1
  have hdom := (Classical.choose_spec hex).2
  have hf := (regularized_finite_of_cp_domination N M hc hdom).2
  let hcapex := finite_cap_of_cp_domination N M hc hdom
  let cap := Classical.choose hcapex
  have hcap := (Classical.choose_spec hcapex).1
  have hblock := (Classical.choose_spec hcapex).2
  exact {
    relative_finite := hfin
    renyi_finite := hf
    order_mono := by
      intro α hα β hβ hαβ
      apply ENNReal.toReal_mono (hf β hβ)
      simp_rw [regularizedRenyi_eq_input_sup]
      exact iSup_mono fun i => hmono i hα hβ hαβ
    relative_le_renyi := fun α hα => ENNReal.toReal_mono (hf α hα)
      (regularizedRelative_le_regularizedRenyi_of_mono N M hmono hα)
    cap := cap
    threshold_le_cap := hcap
    block_cap := hblock
    block_slack := fun n γ hγ =>
      hockeySlackAttainment_of_one_le (channelPower N n) (channelPower M n) hγ
    power_scaling := fun α hα _ n hn => regularizedRenyi_power_scaling hα N M hn }





end QuantumChannelContinuity


