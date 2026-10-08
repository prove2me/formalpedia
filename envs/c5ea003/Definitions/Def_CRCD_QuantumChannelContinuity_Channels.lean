-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_Channels
-- name    : CRCD_QuantumChannelContinuity_Channels
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:38:06.602211+00:00
-- url     : https://prove2.me/theorems/72d967b8-5984-478a-8159-c7b809caaa28
-- title:
--   Stabilized channel divergences from pure inputs
-- statement:
--   A pure input is a unit vector $\psi$. Its density operator is $|\psi\rangle\langle\psi|$. For nonzero finite-dimensional complex Hilbert spaces $H,K$, a completely positive trace-preserving map $N:H\to K$, and a density state on $H\otimes H$, the amplified output is $(N\otimes\mathrm{id}_H)(\rho)$ on $K\otimes H$. Define
--   $$
--   D_\alpha(N\Vert M)=\sup_{\|\psi\|=1}D_\alpha((N\otimes\mathrm{id})(\psi\psi^*)\Vert(M\otimes\mathrm{id})(\psi\psi^*))^{+},\qquad D(N\Vert M)=\sup_{\|\psi\|=1}D((N\otimes\mathrm{id})(\psi\psi^*)\Vert(M\otimes\mathrm{id})(\psi\psi^*))^{+}.
--   $$
--   Here $\psi\in H\otimes H$, the channel acts on the first factor, and $x^{+}$ denotes the Lean conversion from extended reals to nonnegative extended reals, truncating negative values to zero and preserving $+\infty$. Thus both channel quantities take values in $[0,+\infty]$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/Channels.lean#L26-L138

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

/-- A normalized pure input vector. -/
structure PureInput (H : Type u) [Qudit H] where
  vector : H
  norm_one : ‖vector‖ = 1

noncomputable instance [Nontrivial H] : Nonempty (PureInput H) := by
  let b := stdOrthonormalBasis ℂ H
  let i : Fin (Module.finrank ℂ H) := ⟨0, Module.finrank_pos⟩
  exact ⟨⟨b i, b.norm_eq_one i⟩⟩

/-- The rank-one density operator of a pure input. -/
noncomputable def PureInput.density (ψ : PureInput H) : DensityState H where
  op := outer_product ψ.vector ψ.vector
  nonneg := outer_product_self_nonneg _
  trace_one := by
    rw [trace_outer_product, inner_self_eq_norm_sq_to_K, ψ.norm_one]
    norm_num

/-- Amplification acts as the channel on the first tensor factor. -/
theorem amplifyWithId_tensor (E : CPTP H K) (A B : L H) :
    amplifyWithId E.toLinearMap (TensorProduct.map A B) =
      TensorProduct.map (E.toFun A) B := by
  rw [← l_tensor_equiv_symm_tmul, ← l_tensor_equiv_symm_tmul]
  simp [amplifyWithId]

/-- The actual amplification preserves trace on arbitrary, possibly entangled,
operators. The proof extends from simple tensors by linearity. -/
theorem trace_amplifyWithId (E : CPTP H K) (ρ : L (H ⊗[ℂ] H)) :
    Tr (amplifyWithId E.toLinearMap ρ) = Tr ρ := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := H) (ℋ₂ := H)).symm.surjective ρ
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul A B =>
      rw [l_tensor_equiv_symm_tmul, amplifyWithId_tensor,
        LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct', ← E.trace_map]
  | add x y hx hy => simp_all

/-- A stabilized output is a normalized positive density operator. -/
noncomputable def amplifiedOutput (E : CPTP H K)
    (ρ : DensityState (H ⊗[ℂ] H)) : DensityState (K ⊗[ℂ] H) where
  op := amplifyWithId E.toLinearMap ρ.op
  nonneg := cp_to_tensor E.toLinearMap ⟨E.toCompletelyPositiveMap, rfl⟩ ρ.op ρ.nonneg
  trace_one := (trace_amplifyWithId E ρ.op).trans ρ.trace_one

instance tensorQuditNontrivial [Nontrivial H] [Nontrivial K] :
    Nontrivial (H ⊗[ℂ] K) :=
  (Module.finrank_pos_iff (R := ℂ)).mp (by
    rw [Module.finrank_tensorProduct (R := ℂ) (S := ℂ) (M := H) (M' := K)]
    exact Nat.mul_pos (Module.finrank_pos (R := ℂ) (M := H))
      (Module.finrank_pos (R := ℂ) (M := K)))

variable [Nontrivial H] [Nontrivial K]

/-- Stabilized sandwiched Rényi divergence, optimized over pure entangled
inputs with a reference copy of the input space. -/
noncomputable def channelRenyi (α : ℝ) (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ ψ : PureInput (H ⊗[ℂ] H),
    (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal

/-- Stabilized channel relative entropy using the same pure-input domain. -/
noncomputable def channelRelative (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ ψ : PureInput (H ⊗[ℂ] H),
    (stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal

/-- Every tested input is bounded by the concrete stabilized divergence. -/
theorem stateRenyi_le_channel (N M : CPTP H K) (α : ℝ)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal ≤
      channelRenyi α N M := by
  unfold channelRenyi
  exact le_iSup (fun φ : PureInput (H ⊗[ℂ] H) =>
    (stateRenyi α (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)).toENNReal) ψ

theorem stateRelative_le_channel (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    (stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal ≤
      channelRelative N M := by
  unfold channelRelative
  exact le_iSup (fun φ : PureInput (H ⊗[ℂ] H) =>
    (stateRelative (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)).toENNReal) ψ

/-- An upper bound on the concrete channel supremum bounds every input in
the support-aware extended-real convention. -/
theorem stateRenyi_le_of_channel_le (N M : CPTP H K) {α a : ℝ}
    (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1) (ha : 0 ≤ a)
    (hD : channelRenyi α N M ≤ ENNReal.ofReal a)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density) ≤ (a : EReal) := by
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    ((stateRenyi_le_channel N M α ψ).trans hD)
  rw [EReal.coe_toENNReal (stateRenyi_nonneg hα hα1 _ _), EReal.coe_ennreal_ofReal,
    max_eq_left ha] at h
  exact h

theorem stateRelative_le_of_channel_le (N M : CPTP H K) {a : ℝ}
    (ha : 0 ≤ a) (hD : channelRelative N M ≤ ENNReal.ofReal a)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density) ≤ (a : EReal) := by
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    ((stateRelative_le_channel N M ψ).trans hD)
  rw [EReal.coe_toENNReal (stateRelative_nonneg _ _), EReal.coe_ennreal_ofReal,
    max_eq_left ha] at h
  exact h

/-- A genuine support-mismatched stabilized output forces infinite channel
relative entropy. No abstract infinity witness is assumed for this implication. -/
theorem channelRelative_top_of_support_mismatch (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H))
    (hs : ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op) :
    channelRelative N M = ⊤ := by
  apply top_unique
  have h := stateRelative_le_channel N M ψ
  simpa [stateRelative_eq_top_of_not_support _ _ hs] using h



end QuantumChannelContinuity


