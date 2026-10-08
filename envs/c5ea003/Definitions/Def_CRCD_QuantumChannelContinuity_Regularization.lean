-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
-- name    : CRCD_QuantumChannelContinuity_Regularization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:12:37.768608+00:00
-- url     : https://prove2.me/theorems/da9d434a-798d-4728-a825-1be33bd877f9
-- title:
--   Tensor powers and regularized channel divergences
-- statement:
--   For nonzero finite-dimensional complex Hilbert spaces, define $H_0=\mathbb C$ in the chosen one-dimensional Euclidean model and $H_{n+1}=H\otimes H_n$. The channel powers satisfy $N_0=\mathrm{id}$ and $N_{n+1}=N\otimes N_n$. Their stabilized divergences are the block quantities $B_\alpha(n)=D_\alpha(N_n\Vert M_n)$ and $B(n)=D(N_n\Vert M_n)$. Define
--   $$
--   D_\alpha^{\mathrm{reg}}(N\Vert M)=\sup_{n>0}\frac{B_\alpha(n)}{n},\qquad D^{\mathrm{reg}}(N\Vert M)=\sup_{n>0}\frac{B(n)}{n}.
--   $$
--   These suprema take values in the nonnegative extended reals. The block testing quantity at rate $r$ is $E_{2^{nr}}(N_n\Vert M_n)$, using the stabilized hockey-stick divergence. Positive block lengths are explicit in the regularization.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/Regularization.lean#L23-L115

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
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
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
# Concrete tensor powers and block-supremum divergences

The regularized quantities are defined as suprema over positive block lengths.
Their identification with limits via superadditivity/Fekete is a separate
obligation, not asserted by these definitions.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

/-- A bundled nonzero finite-dimensional Hilbert space for dependent tensor
power recursion. -/
structure HilbertBlock where
  Space : Type
  qudit : Qudit Space
  nontrivial : Nontrivial Space

attribute [instance] HilbertBlock.qudit HilbertBlock.nontrivial

/-- A canonical tensor power, with the one-dimensional space as unit. -/
noncomputable def tensorPowerSpace (H : Type) [Qudit H] [Nontrivial H] : ℕ → HilbertBlock
  | 0 => ⟨EuclideanSpace ℂ (Fin 1), inferInstance, inferInstance⟩
  | n + 1 => ⟨H ⊗[ℂ] (tensorPowerSpace H n).Space, inferInstance, inferInstance⟩

abbrev TensorPower (H : Type) [Qudit H] [Nontrivial H] (n : ℕ) :=
  (tensorPowerSpace H n).Space

/-- The identity CPTP channel. -/
noncomputable def identityChannel (H : Type) [Qudit H] : CPTP H H where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_cstarMatrix_nonneg' k X hX := by simpa only [CStarMatrix.map_id] using hX
  trace_map _ := rfl

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- Actual tensor powers of the supplied CPTP map. -/
noncomputable def channelPower (N : CPTP H K) :
    (n : ℕ) → CPTP (TensorPower H n) (TensorPower K n)
  | 0 => identityChannel _
  | n + 1 => tensorChannel N (channelPower N n)

/-- Stabilized Rényi divergence of the actual `n`-fold tensor powers. -/
noncomputable def blockRenyi (α : ℝ) (N M : CPTP H K) (n : ℕ) : ℝ≥0∞ :=
  channelRenyi α (channelPower N n) (channelPower M n)

/-- Stabilized relative entropy of the actual `n`-fold tensor powers. -/
noncomputable def blockRelative (N M : CPTP H K) (n : ℕ) : ℝ≥0∞ :=
  channelRelative (channelPower N n) (channelPower M n)

/-- The block-supremum definition of regularized channel Rényi divergence. -/
noncomputable def regularizedRenyi (α : ℝ) (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRenyi α N M n / (n : ℝ≥0∞)

/-- The block-supremum definition of regularized channel relative entropy. -/
noncomputable def regularizedRelative (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRelative N M n / (n : ℝ≥0∞)

/-- Concrete block testing quantity at the manuscript's threshold. -/
noncomputable def blockTesting (N M : CPTP H K) (n : ℕ) (r : ℝ) : ℝ :=
  channelHockey ((2 : ℝ) ^ ((n : ℝ) * r)) (channelPower N n) (channelPower M n)

theorem blockRenyi_le_regularized (α : ℝ) (N M : CPTP H K) {n : ℕ} (hn : 0 < n) :
    blockRenyi α N M n ≤ regularizedRenyi α N M * (n : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mp
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

theorem blockRelative_le_regularized (N M : CPTP H K) {n : ℕ} (hn : 0 < n) :
    blockRelative N M n ≤ regularizedRelative N M * (n : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mp
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

theorem blockTesting_nonneg (N M : CPTP H K) (n : ℕ) (r : ℝ) :
    0 ≤ blockTesting N M n r :=
  channelHockey_nonneg (Real.rpow_nonneg (by norm_num) _) _ _



/-- The concrete weak bound uses the actual finite regularized divergence;
all quantum testing steps and the block supremum bound are proved. -/
theorem regularized_weak_testing (N M : CPTP H K)
    (hfin : regularizedRelative N M ≠ ⊤) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    blockTesting N M n r ≤ (regularizedRelative N M).toReal / r +
      1 / ((n : ℝ) * r) := by
  apply block_channelHockey_relative_bound _ _ hn hr ENNReal.toReal_nonneg
  change blockRelative N M n ≤ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_toReal hfin]
  simpa [mul_comm] using blockRelative_le_regularized N M hn

/-- The concrete exponential bound, expressed in terms of the actual
finite block-supremum Rényi divergence. -/
theorem regularized_renyi_testing (N M : CPTP H K) {α : ℝ} (hα : 1 < α)
    (hfin : regularizedRenyi α N M ≠ ⊤) {n : ℕ} (hn : 0 < n) (ell : ℝ) :
    blockTesting N M n ell ≤
      (2 : ℝ) ^ (-(n : ℝ) * (α - 1) * (ell - (regularizedRenyi α N M).toReal)) := by
  apply block_channelHockey_renyi_bound _ _ n hα ENNReal.toReal_nonneg
  change blockRenyi α N M n ≤ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_toReal hfin]
  simpa [mul_comm] using blockRenyi_le_regularized α N M hn

end QuantumChannelContinuity


