-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SlackTraceBound
-- name    : CRCD_QuantumChannelContinuity_SlackTraceBound
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:30:28.142842+00:00
-- url     : https://prove2.me/theorems/a89a623e-fd36-47a7-9cd5-682f7dee9ec7
-- title:
--   Partial-trace bounds for Choi operators and amplified outputs
-- statement:
--   Let $\Phi$ be an arbitrary complex-linear superoperator from operators on $A$ to operators on $B$, with $A$ nonzero and both Hilbert spaces finite-dimensional. If its Choi operator satisfies
--
--   $$
--   \operatorname{Tr}_B J(\Phi)\le\varepsilon I_A
--   $$
--
--   for a real $\varepsilon$, then
--
--   $$
--   \operatorname{Re}\operatorname{Tr}\Phi(|a\rangle\langle a|)\le\varepsilon\|a\|^2,\qquad \operatorname{Re}\operatorname{Tr}[(\Phi\otimes\mathrm{id}_A)(|\psi\rangle\langle\psi|)]\le\varepsilon\|\psi\|^2.
--   $$
--
--   The second estimate holds for every $\psi\in A\otimes A$. Complete positivity of $\Phi$ and nonnegativity of $\varepsilon$ are not premises here. The supporting identities, with the reference factor on the right, are
--
--   $$
--   \operatorname{Tr}[(I_B\otimes S)X(I_B\otimes S)^\dagger]=\operatorname{Tr}[S^\dagger S\,\operatorname{Tr}_B X],\qquad (I_B\otimes S)^\dagger(I_B\otimes S)=I_B\otimes(S^\dagger S).
--   $$
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SlackTraceBound.lean#L23-L75

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
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPPartialTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTester
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




/-! # From a Choi marginal bound to the uniform pure-input trace bound -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B : Type u} [Qudit A] [Qudit B]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

theorem environment_gram (S : L A) :
    (LinearMap.adjoint (environmentMap (B := B) S)).comp (environmentMap (B := B) S) =
      environmentMap (B := B) ((LinearMap.adjoint S).comp S) := by
  simp [environmentMap,TensorProduct.adjoint_map,← TensorProduct.map_comp]

/-- The trace of a weighted Choi operator is the pairing with its reference marginal. -/
theorem trace_weighted_choi (X : L (B ⊗[ℂ] A)) (S : L A) :
    Tr (krausTerm (environmentMap (B := B) S) X) =
      Tr (((LinearMap.adjoint S).comp S) * leftPartialTrace X) := by
  let U := environmentMap (B := B) S
  have hcycle : Tr (krausTerm U X) = Tr (((LinearMap.adjoint U).comp U).comp X) := by
    have h := LinearMap.trace_comp_comm' (U.comp X) (LinearMap.adjoint U)
    simpa only [krausTerm,LinearMap.comp_assoc] using h.symm
  rw [hcycle]
  change Tr (((LinearMap.adjoint (environmentMap (B := B) S)).comp
    (environmentMap (B := B) S)).comp X) = _
  rw [environment_gram]
  exact (leftPartialTrace_pair X ((LinearMap.adjoint S).comp S)).symm

variable [Nontrivial A]

/-- A Choi marginal bound controls the trace for every entangled pure input. -/
theorem amplified_trace_le_of_choi_marginal (Φ : T A B) (ε : ℝ)
    (hbound : leftPartialTrace (choi (stdOrthonormalBasis ℂ A).toBasis Φ) ≤
      (ε : ℂ) • (1 : L A)) (ψ : A ⊗[ℂ] A) :
    (Tr (amplifyWithId Φ (outer_product ψ ψ))).re ≤ ε * ‖ψ‖ ^ 2 := by
  obtain ⟨S,rfl⟩ := reference_choiVector_surjective (A := A) ψ
  rw [amplify_weighted_choi,trace_weighted_choi,norm_reference_choiVector_sq]
  let G : L A := (LinearMap.adjoint S).comp S
  have hG : 0 ≤ G := by change 0 ≤ star S * S; exact star_mul_self_nonneg S
  have hp := trace_product_nonneg hG (sub_nonneg.mpr hbound)
  simp only [mul_sub,mul_smul_comm,mul_one,map_sub,map_smul,Complex.sub_re,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp
  exact sub_nonneg.mp hp

/-- In particular, the Choi marginal bound gives the exact vector trace
inequality used by `HockeySlackAttainment`, without a dimension factor. -/
theorem trace_le_of_choi_marginal (Φ : T A B) (ε : ℝ)
    (hbound : leftPartialTrace (choi (stdOrthonormalBasis ℂ A).toBasis Φ) ≤
      (ε : ℂ) • (1 : L A)) (a : A) :
    (Tr (Φ (outer_product a a))).re ≤ ε * ‖a‖ ^ 2 := by
  let r : PureInput A := Classical.choice inferInstance
  have h := amplified_trace_le_of_choi_marginal Φ ε hbound (a ⊗ₜ[ℂ] r.vector)
  have htrace : Tr (amplifyWithId Φ (outer_product (a ⊗ₜ[ℂ] r.vector) (a ⊗ₜ[ℂ] r.vector))) =
      Tr (Φ (outer_product a a)) := by
    rw [← l_tensor_equiv_symm_outer_product,l_tensor_equiv_symm_tmul]
    change Tr (tensorSuperoperator Φ (LinearMap.id : T A A)
      (TensorProduct.map (outer_product a a) (outer_product r.vector r.vector))) = _
    rw [tensorSuperoperator_apply,LinearMap.trace_tensorProduct']
    change Tr (Φ (outer_product a a)) * Tr r.density.op = _
    rw [r.density.trace_one,mul_one]
  rw [htrace,TensorProduct.norm_tmul,r.norm_one,mul_one] at h
  exact h

end QuantumChannelContinuity


