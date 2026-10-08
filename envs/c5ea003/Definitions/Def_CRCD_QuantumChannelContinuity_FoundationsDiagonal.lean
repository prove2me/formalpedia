-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
-- name    : CRCD_QuantumChannelContinuity_FoundationsDiagonal
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:39:56.010257+00:00
-- url     : https://prove2.me/theorems/230b3c8e-345f-40d0-8ee0-c274c78c525c
-- title:
--   Spectral formulas for measured quasi-entropy and relative entropy
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, let nonnegative operators $\rho,\sigma$ have a common orthonormal eigenbasis with eigenvalues $p_i,q_i$. For the real exponent $\alpha$, putting $\beta=(1-\alpha)/(2\alpha)$, the formal sandwiched quasi-entropy obeys the exact scalar expression
--
--   $$
--   Q_\alpha(\rho,\sigma)=\sum_i(q_i^\beta p_iq_i^\beta)^\alpha.
--   $$
--
--   The same expression holds for measured density states, with $p_i,q_i$ the probabilities of a finite nonempty POVM. Powers and division use the total real operations of the formal definitions, so the unsimplified product expression is retained at boundary values.
--
--   For support-included density states diagonal in that basis, their relative entropy in bits is
--
--   $$
--   D(\rho\|\sigma)=\frac{\sum_i p_i(\ln p_i-\ln q_i)}{\ln2},
--   $$
--
--   with the formal total-log convention at zero. Support inclusion forces $p_i=0$ whenever $q_i=0$. For any nonnegative operator $A$ and nonzero eigenvector $Av=rv$, functional calculus gives $A^tv=r^tv$ for every real $t$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FoundationsDiagonal.lean#L19-L113

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
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
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



/-! # Evaluation of quantum divergences on measured, diagonal states -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Real operator powers act on an eigenvector by real scalar powers. -/
theorem rpow_apply_eigenvector {A : L H} (hA : 0 ≤ A) (t : ℝ)
    {v : H} (hv : v ≠ 0) {r : ℝ} (hr : A v = (r : ℂ) • v) :
    CFC.rpow A t v = ((r ^ t : ℝ) : ℂ) • v := by
  have hsa : IsSelfAdjoint A := (LinearMap.nonneg_iff_isPositive A).mp hA |>.isSelfAdjoint
  have heq : CFC.rpow A t = cfc (fun x : ℝ => x ^ t) A := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real (ha := hA)
  rw [heq]
  exact cfc_real_apply_eigenvector hsa (fun x => x ^ t) hr (mem_spectrum_real_of_eigenvector hv hr)

/-- Support inclusion forces every zero eigenvalue of the denominator to
have zero weight in the numerator in a common eigenbasis. -/
theorem zero_of_support_common_eigenvector {ρ σ : L H} (hs : suppLE ρ σ)
    {v : H} (hv : v ≠ 0) {p q : ℝ}
    (hp : ρ v = (p : ℂ) • v) (hq : σ v = (q : ℂ) • v) (hq0 : q = 0) : p = 0 := by
  have hvker : v ∈ LinearMap.ker σ := by
    rw [LinearMap.mem_ker, hq, hq0]
    simp
  have hz := LinearMap.mem_ker.mp (hs hvker)
  rw [hp] at hz
  have hp0 := (smul_eq_zero.mp hz).resolve_right hv
  exact_mod_cast hp0

/-- The sandwiched quantum trace evaluates to its classical sum on a shared
orthonormal eigenbasis, including zero eigenvalues. -/
theorem sandwichedQuasi_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : L H) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (p q : ι → ℝ) (hp : ∀ i, ρ (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ (b i) = (q i : ℂ) • b i) (α : ℝ) :
    (sandwichedQuasi α ρ σ).re =
      ∑ i, (q i ^ ((1 - α) / (2 * α)) * p i * q i ^ ((1 - α) / (2 * α))) ^ α := by
  let t := (1 - α) / (2 * α)
  let S := CFC.rpow σ t
  have hS : ∀ i, S (b i) = ((q i ^ t : ℝ) : ℂ) • b i := by
    intro i
    exact rpow_apply_eigenvector hσ t (b.orthonormal.ne_zero i) (hq i)
  have hM : 0 ≤ S * ρ * S := by
    exact conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hMeig : ∀ i, (S * ρ * S) (b i) =
      ((q i ^ t * p i * q i ^ t : ℝ) : ℂ) • b i := by
    intro i
    simp only [Module.End.mul_apply, hS, map_smul, hp, smul_smul]
    congr 1
    push_cast
    ring
  have hR : ∀ i, CFC.rpow (S * ρ * S) α (b i) =
      (((q i ^ t * p i * q i ^ t) ^ α : ℝ) : ℂ) • b i := by
    intro i
    exact rpow_apply_eigenvector hM α (b.orthonormal.ne_zero i) (hMeig i)
  change (Tr (CFC.rpow (S * ρ * S) α)).re = _
  rw [LinearMap.trace_eq_sum_inner (T := CFC.rpow (S * ρ * S) α) b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hR, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re]

/-- Umegaki relative entropy is the classical diagonal log expression on a
common eigenbasis. The separate support-aware definition still assigns
infinity when the support condition fails. -/
theorem umegaki_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : DensityState H)
    (p q : ι → ℝ) (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i)
    (hs : suppLE ρ.op σ.op) :
    stateRelative ρ σ = ((∑ i, p i * (Real.log (p i) - Real.log (q i))) / Real.log 2 : ℝ) := by
  rw [stateRelative_eq_formula ρ σ hs]
  congr 2
  rw [LinearMap.trace_eq_sum_inner (T := ρ.op * (CFC.log ρ.op - CFC.log σ.op)) b,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpLog : CFC.log ρ.op (b i) = (Real.log (p i) : ℂ) • b i :=
    cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg ρ.nonneg)
      Real.log (hp i) (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (hp i))
  have hqLog : CFC.log σ.op (b i) = (Real.log (q i) : ℂ) • b i :=
    cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg σ.nonneg)
      Real.log (hq i) (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (hq i))
  change (inner ℂ (b i) (ρ.op ((CFC.log ρ.op - CFC.log σ.op) (b i)))).re = _
  simp only [LinearMap.sub_apply, hpLog, hqLog, map_sub, map_smul, hp,
    inner_sub_right, inner_smul_right, b.inner_eq_one, mul_one,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Applying an arbitrary POVM makes the quantum sandwiched trace exactly the
classical expression in the actual Born probabilities. -/
theorem measured_sandwichedQuasi {H : Type} [Qudit H] [Nontrivial H]
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : POVM H ι) (ρ σ : DensityState H) (α : ℝ) :
    (sandwichedQuasi α (ρ.map M.channel).op (σ.map M.channel).op).re =
      ∑ i, (M.probability σ i ^ ((1 - α) / (2 * α)) * M.probability ρ i *
        M.probability σ i ^ ((1 - α) / (2 * α))) ^ α := by
  exact sandwichedQuasi_common_eigenbasis (EuclideanSpace.basisFun ι ℂ)
    _ _ (ρ.map M.channel).nonneg (σ.map M.channel).nonneg
    (M.probability ρ) (M.probability σ)
    (M.channel_apply_basis_probability ρ) (M.channel_apply_basis_probability σ) α

end QuantumChannelContinuity


