-- Prove2me | solution 1 for QuantumChannelContinuity.complex_trace_holder_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T03:54:14.99788+00:00
-- url     : https://prove2.me/submissions/75b867f3-2e4f-4b0c-af9c-9f7561bc4363

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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Theorems.Thm_QuantumChannelContinuity_complex_trace_holder_majorant

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Complex trace Hölder

The bound is proved from Hilbert–Schmidt Cauchy–Schwarz and the already
proved positive-operator trace Hölder inequality. Positive regularization
handles all singular operators.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder MatrixOrder NNReal Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {H : Type u} [Qudit H]









/-- Positive powers vary continuously over the entire nonnegative cone. -/
private theorem operator_rpow_continuousOn_nonneg [Nontrivial H] {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun X : L H => CFC.rpow X t) {X : L H | 0 ≤ X} := by
  have hmem : (Set.univ : Set ℝ≥0) ∈ 𝓝ˢ (⋃ X ∈ {X : L H | 0 ≤ X}, spectrum ℝ≥0 X) :=
    Filter.univ_mem
  exact (continuousOn_id : ContinuousOn (fun X : L H => X) {X : L H | 0 ≤ X}).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ t)) hmem (ha' := fun X hX => hX)
    (hf := NNReal.continuousOn_rpow_const (.inr ht))





end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
universe u
variable {H : Type u} [Qudit H]
open QuantumChannelContinuity in
/-- Removing the strictly positive majorant by positive regularization. -/
theorem solution [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (A B : L H) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have hp0 := hpq.pos
  let X : ℝ → L H := fun ε => A * star A + (ε : ℂ) • 1
  have hXpd (ε : ℝ) (hε : 0 < ε) : X ε ∈ pdSetLM :=
    pdSetLM_add_nonneg (mul_star_self_nonneg A) (pos_smul_one_pdSetLM hε)
  have hAX (ε : ℝ) (hε : 0 < ε) : A * star A ≤ X ε := by
    exact le_add_of_nonneg_right (smul_nonneg (by exact_mod_cast hε.le : (0 : ℂ) ≤ ε) zero_le_one)
  have hXlim : Filter.Tendsto X (𝓝[>] (0 : ℝ)) (𝓝 (A * star A)) := by
    have hc : Continuous X := by dsimp [X]; fun_prop
    simpa [X] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hwithin : Filter.Tendsto X (𝓝[>] (0 : ℝ)) (𝓝[{Y : L H | 0 ≤ Y}] (A * star A)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hXlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact nonneg_of_pdSetLM (hXpd ε hε)
  have hpow := ((operator_rpow_continuousOn_nonneg (H := H)
    (show 0 ≤ p / 2 by positivity)) (A * star A) (mul_star_self_nonneg A)).tendsto.comp hwithin
  have htrace := Complex.continuous_re.continuousAt.tendsto.comp
    (((LinearMap.trace ℂ H).continuous_of_finiteDimensional.tendsto _).comp hpow)
  have hr := ((Real.continuousAt_rpow_const _ (1 / p) (Or.inr (by positivity))).tendsto.comp htrace).mul_const
    ((Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hr
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact complex_trace_holder_majorant hpq hp2 A B (X ε) (hXpd ε hε) (hAX ε hε)

end
