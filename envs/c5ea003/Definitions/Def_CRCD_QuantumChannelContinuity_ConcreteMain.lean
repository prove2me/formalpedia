-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ConcreteMain
-- name    : CRCD_QuantumChannelContinuity_ConcreteMain
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:17:15.495646+00:00
-- url     : https://prove2.me/theorems/f9de7fb9-2935-45b1-83fe-3f95643b5074
-- title:
--   Block inputs and finite analytic input records
-- statement:
--   A block input consists of a positive natural number $n$ and a unit vector in $H_n\otimes H_n$. Its Rényi and relative divergences are the corresponding amplified state divergences, converted to nonnegative extended reals and divided by $n$. Their suprema recover the block regularizations. The auxiliary record `RemainingFiniteInputs` packages finiteness of relative entropy and of every regularized Rényi divergence above order one, monotonicity above one, the relative-to-Rényi lower bound, a real cap, and the raw Schatten estimate for block testing quantities. A value of this record supplies hypotheses for the scalar finite-limit argument; the record definition alone does not assert their validity for arbitrary channels.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ConcreteMain.lean#L29-L101

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
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
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
# Concrete channel divergences and the scalar continuity interface

States, channels, tensor powers, regularized quantities and testing functions
are concrete quantum objects. The testing bounds are proved here.
`RemainingFiniteInputs` isolates the finite scalar estimates;
`QuantumMain.lean` derives the raw estimate, and `ContinuityAssembly.lean`
constructs the record from the proved state-order and operator results.
`Main.lean` exports the unconditional theorem, including the infinite case.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ENNReal Topology TensorProduct

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- Scalar inputs for the finite right-limit argument. The raw estimate is
assembled by `QuantumThresholdInputs.toRemaining` in `QuantumMain.lean`;
`ContinuityAssembly.lean` constructs the record in the finite branch. -/
structure RemainingFiniteInputs (N M : CPTP H K) where
  relative_finite : regularizedRelative N M ≠ ⊤
  renyi_finite : ∀ α, 1 < α → regularizedRenyi α N M ≠ ⊤
  order_mono : MonotoneOn (fun α => (regularizedRenyi α N M).toReal) (Ioi 1)
  relative_le_renyi : ∀ α, 1 < α →
    (regularizedRelative N M).toReal ≤ (regularizedRenyi α N M).toReal
  cap : ℝ
  raw_schatten :
    let a := fun α => (regularizedRenyi α N M).toReal
    let dPlus := sInf (a '' Ioi 1)
    ∀ r, 0 ≤ r → r < dPlus → ∀ t : ℝ, 1 ≤ t →
      ∀ n : ℕ, t < (n : ℝ) → 2 * t ≤ (n : ℝ) →
      (2 : ℝ) ^ (t * dPlus / 2) ≤
        ChannelContinuity.rawSchattenRhs n t r dPlus cap
          (Real.sqrt (blockTesting N M n r))
          (Real.sqrt (blockTesting N M n (dPlus + 1 / (t * t))))

/-- Construct the analytical input record with all quantum testing fields
proved from the concrete channel definitions. -/
noncomputable def RemainingFiniteInputs.analytic {N M : CPTP H K}
    (h : RemainingFiniteInputs N M) : ChannelContinuity.FiniteAnalyticInputs where
  d := (regularizedRelative N M).toReal
  renyi α := (regularizedRenyi α N M).toReal
  cap := h.cap
  testing := blockTesting N M
  d_nonneg := ENNReal.toReal_nonneg
  order_mono := h.order_mono
  relative_le_renyi := h.relative_le_renyi
  testing_nonneg := blockTesting_nonneg N M
  weak_testing _ hr _ hn := regularized_weak_testing N M h.relative_finite hn hr
  renyi_testing α hα ell _ _ hn :=
    regularized_renyi_testing N M hα (h.renyi_finite α hα) hn ell
  raw_schatten := h.raw_schatten



/-- A positive block length and an actual pure input to its stabilized channel. -/
abbrev BlockInput (H : Type) [Qudit H] [Nontrivial H] :=
  (n : {n : ℕ // 0 < n}) ×
    PureInput (TensorPower H n.val ⊗[ℂ] TensorPower H n.val)

noncomputable def inputRenyi (N M : CPTP H K) (α : ℝ) (i : BlockInput H) : ℝ≥0∞ :=
  (stateRenyi α (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).toENNReal / (i.1.val : ℝ≥0∞)

noncomputable def inputRelative (N M : CPTP H K) (i : BlockInput H) : ℝ≥0∞ :=
  (stateRelative (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).toENNReal / (i.1.val : ℝ≥0∞)

theorem regularizedRenyi_eq_input_sup (N M : CPTP H K) (α : ℝ) :
    regularizedRenyi α N M = ⨆ i : BlockInput H, inputRenyi N M α i := by
  simp only [regularizedRenyi, blockRenyi, channelRenyi, ENNReal.iSup_div,
    inputRenyi, iSup_sigma, iSup_subtype]

theorem regularizedRelative_eq_input_sup (N M : CPTP H K) :
    regularizedRelative N M = ⨆ i : BlockInput H, inputRelative N M i := by
  simp only [regularizedRelative, blockRelative, channelRelative, ENNReal.iSup_div,
    inputRelative, iSup_sigma, iSup_subtype]







end QuantumChannelContinuity


