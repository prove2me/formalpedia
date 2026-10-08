-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
-- name    : CRCD_QuantumChannelContinuity_SDPCone
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:46:48.87783+00:00
-- url     : https://prove2.me/theorems/0e74b904-9621-42a9-9155-e24553e9a3e1
-- title:
--   The primal semidefinite slack cone
-- statement:
--   For a real linear map $\tau$ between spaces of Hermitian operators on nonzero finite-dimensional complex Hilbert spaces, define the cone containing the origin
--   $$
--   \mathcal C_\tau=\{(D,Z):\exists Q\ge0,\ D\le Q\text{ and }\tau(Q)\le Z\}.
--   $$
--   The witness $Q$ is a positive upper slack for $D$. Closure under addition and nonnegative real scalar multiplication is built into the cone. Closedness assumes that $\tau$ preserves the real trace; no positivity premise on $\tau$ is required. The separation interface additionally supplies a real trace-pairing adjoint and an infeasible pair $(D,Z)$, and obtains positive dual witnesses. These are the finite-dimensional interfaces needed for slack attainment.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SDPCone.lean#L29-L122

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
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
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
# The closed semidefinite slack cone and exact separation

Closedness, including attainment at the boundary, follows from the trace bound
on a positive slack operator. Hahn–Banach separation then supplies positive
operator witnesses satisfying the dual semidefinite constraints.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H K : Type u} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Primal semidefinite slack cone for a trace-preserving linear map. -/
noncomputable def sdpSlackCone (τ : Hermitian H →ₗ[ℝ] Hermitian K) :
    PointedCone ℝ (Hermitian H × Hermitian K) where
  carrier := {p | ∃ Q : Hermitian H, 0 ≤ Q ∧ p.1 ≤ Q ∧ τ Q ≤ p.2}
  zero_mem' := ⟨0, le_rfl, le_rfl, by simp⟩
  add_mem' := by
    rintro x y ⟨Q,hQ,hx,hτQ⟩ ⟨R,hR,hy,hτR⟩
    exact ⟨Q+R, add_nonneg hQ hR, add_le_add hx hy, by simpa using add_le_add hτQ hτR⟩
  smul_mem' := by
    rintro r p ⟨Q,hQ,hp,hτQ⟩
    refine ⟨(r : ℝ) • Q, hermitian_smul_nonneg r.property hQ,
      hermitian_smul_mono r.property hp, ?_⟩
    simpa using hermitian_smul_mono r.property hτQ

/-- The slack cone is closed: positive slacks in a convergent feasible sequence
have bounded trace, hence bounded norm and a convergent subsequence. -/
theorem sdpSlackCone_isClosed (τ : Hermitian H →ₗ[ℝ] Hermitian K)
    (htrace : ∀ Q, hermitianTrace (H := K) (τ Q) = hermitianTrace (H := H) Q) :
    IsClosed (sdpSlackCone τ : Set (Hermitian H × Hermitian K)) := by
  apply IsSeqClosed.isClosed
  intro p z hp hz
  choose Q hQ hx hτ using hp
  have htr : Tendsto (fun n => hermitianTrace (H := K) (p n).2) atTop
      (𝓝 (hermitianTrace (H := K) z.2)) :=
    (hermitianTrace (H := K)).continuous_of_finiteDimensional.tendsto _ |>.comp ((continuous_snd.tendsto z).comp hz)
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ htr).bddAbove
  have hbound (n) : ‖Q n‖ ≤ C := by
    calc
      ‖Q n‖ ≤ hermitianTrace (H := H) (Q n) := hermitian_norm_le_trace (hQ n)
      _ = hermitianTrace (H := K) (τ (Q n)) := (htrace _).symm
      _ ≤ hermitianTrace (H := K) (p n).2 := hermitianTrace_mono (hτ n)
      _ ≤ C := hC (Set.mem_range_self n)
  obtain ⟨q,_,φ,hφ,hq⟩ := (isCompact_closedBall (0 : Hermitian H) C).tendsto_subseq
    (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n)
  have hpφ := hz.comp hφ.tendsto_atTop
  refine ⟨q, ?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hq (fun n => hQ (φ n))
  · exact le_of_tendsto_of_tendsto' ((continuous_fst.tendsto z).comp hpφ) hq (fun n => hx (φ n))
  · exact le_of_tendsto_of_tendsto'
      (τ.continuous_of_finiteDimensional.tendsto _ |>.comp hq) ((continuous_snd.tendsto z).comp hpφ) (fun n => hτ (φ n))



/-- Exact primal/dual separation for the semidefinite slack problem. This is
a proved finite-dimensional conic duality statement, with no Slater premise. -/
theorem sdpSlack_separation
    (τ : Hermitian H →ₗ[ℝ] Hermitian K) (σ : Hermitian K →ₗ[ℝ] Hermitian H)
    (htrace : ∀ Q, hermitianTrace (H := K) (τ Q) = hermitianTrace (H := H) Q)
    (hadj : ∀ Q Y, hermitianTracePair (H := K) Y (τ Q) =
      hermitianTracePair (H := H) (σ Y) Q)
    (D : Hermitian H) (Z : Hermitian K)
    (hno : ¬ ∃ Q : Hermitian H, 0 ≤ Q ∧ D ≤ Q ∧ τ Q ≤ Z) :
    ∃ W : Hermitian H, ∃ Y : Hermitian K,
      0 ≤ W ∧ 0 ≤ Y ∧ W ≤ σ Y ∧
      hermitianTracePair (H := K) Y Z < hermitianTracePair (H := H) W D := by
  let cone : ProperCone ℝ (Hermitian H × Hermitian K) :=
    ⟨sdpSlackCone τ, sdpSlackCone_isClosed τ htrace⟩
  obtain ⟨f,hf,hneg⟩ := cone.hyperplane_separation_point (x₀ := (D,Z)) hno
  let f₁ := f.toLinearMap.comp (LinearMap.inl ℝ (Hermitian H) (Hermitian K))
  let f₂ := f.toLinearMap.comp (LinearMap.inr ℝ (Hermitian H) (Hermitian K))
  obtain ⟨X,hX⟩ := hermitianTracePair_surjective (H := H) f₁
  obtain ⟨Y,hY⟩ := hermitianTracePair_surjective (H := K) f₂
  have heval (x : Hermitian H) (y : Hermitian K) :
      f (x,y) = hermitianTracePair (H := H) X x + hermitianTracePair (H := K) Y y := by
    rw [hX,hY]
    simpa only [f₁,f₂,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,
      Prod.mk_add_mk,add_zero,zero_add] using (map_add f (x,0) (0,y))
  have hW : 0 ≤ -X := by
    apply (hermitian_nonneg_iff_trace (-X)).mpr
    intro P hP
    have hm : (-P,0) ∈ cone := ⟨0,le_rfl,neg_nonpos.mpr hP,by simp⟩
    have h := hf (-P,0) hm
    simpa only [heval, map_zero, add_zero, map_neg, LinearMap.neg_apply] using h
  have hYn : 0 ≤ Y := by
    apply (hermitian_nonneg_iff_trace Y).mpr
    intro P hP
    have hm : (0,P) ∈ cone := ⟨0,le_rfl,le_rfl,by simpa using hP⟩
    simpa only [heval,map_zero,zero_add] using hf (0,P) hm
  have hle : -X ≤ σ Y := by
    apply sub_nonneg.mp
    apply (hermitian_nonneg_iff_trace (σ Y - -X)).mpr
    intro P hP
    have hm : (P,τ P) ∈ cone := ⟨P,hP,le_rfl,le_rfl⟩
    have h := hf (P,τ P) hm
    rw [heval,hadj] at h
    simpa only [sub_neg_eq_add,map_add,LinearMap.add_apply,add_comm] using h
  refine ⟨-X,Y,hW,hYn,hle,?_⟩
  rw [heval] at hneg
  simp only [map_neg,LinearMap.neg_apply]
  linarith

end QuantumChannelContinuity


