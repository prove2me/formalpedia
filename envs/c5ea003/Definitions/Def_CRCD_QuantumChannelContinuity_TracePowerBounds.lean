-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TracePowerBounds
-- name    : CRCD_QuantumChannelContinuity_TracePowerBounds
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:35:27.573956+00:00
-- url     : https://prove2.me/theorems/da4b4d46-520a-4a49-bf40-2d9c72a792a8
-- title:
--   Trace-power monotonicity and a coarse sandwiched quasi-entropy bound
-- statement:
--   For nonnegative operators $X,Y$ on a finite-dimensional complex Hilbert space, $X\le Y$ implies, for every real $p>1$,
--
--   $$
--   \operatorname{Re}\operatorname{Tr}(X^p)\le\operatorname{Re}\operatorname{Tr}(Y^p).
--   $$
--
--   This is a trace inequality, not an assertion that $X^p\le Y^p$. If $\rho,\sigma\ge0$, $c\ge0$, and $\rho\le c\sigma$, then the real sandwiched quasi-entropy satisfies
--
--   $$
--   Q_p(\rho,\sigma)\le c^p\operatorname{Re}\operatorname{Tr}\sigma\qquad(p>1).
--   $$
--
--   Neither trace-one normalization, commutativity, invertibility, nor a nonzero-operator premise is required for these two inequalities.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TracePowerBounds.lean#L26-L119

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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
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



/-!
# Trace-power bounds at every order above one

A scalar trace moment is monotone even when the corresponding operator power
is not operator-monotone. Trace Hölder proves this directly, and gives the
uniform bounds required to establish finiteness of channel regularizations.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal
namespace QuantumChannelContinuity

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [Qudit H]

/-- Trace powers preserve positive-operator order for every real `p>1`.
The proof uses trace Hölder, with no operator-monotonicity assumption. -/
theorem trace_rpow_re_mono {p : ℝ} (hp : 1 < p)
    {X Y : L H} (hX : X.IsPositive) (hY : Y.IsPositive) (hXY : X ≤ Y) :
    (Tr (CFC.rpow X p)).re ≤ (Tr (CFC.rpow Y p)).re := by
  let q : ℝ := p / (p - 1)
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hpq : p.HolderConjugate q :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  let R := (Tr (CFC.rpow X p)).re
  let S := (Tr (CFC.rpow Y p)).re
  let W := CFC.rpow X (p - 1)
  have hR : 0 ≤ R := trace_rpow_re_nonneg X p
  have hS : 0 ≤ S := trace_rpow_re_nonneg Y p
  have hW : W.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hWq : CFC.rpow W q = CFC.rpow X p := by
    dsimp only [W]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X (p - 1) q (by linarith)
      hpq.symm.nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hX)]
    congr 1
    dsimp [q]
    field_simp
  have hRX : (Tr (X * W)).re = R := by
    rw [LinearMap.trace_mul_comm ℂ X W]
    exact congrArg Complex.re (congrArg Tr (rpow_sub_one_mul_self X hX hp))
  have hbound : R ≤ S ^ (1 / p) * R ^ (1 / q) := by
    calc
      R = (Tr (X * W)).re := hRX.symm
      _ ≤ (Tr (Y * W)).re := trace_mul_re_mono hXY W hW
      _ ≤ S ^ (1 / p) * R ^ (1 / q) := by
        have ht := trace_holder hpq Y W hY hW
        simpa only [hWq] using ht
  change R ≤ S
  rcases eq_or_lt_of_le hR with hz | hRpos
  · rw [← hz]
    exact hS
  · have hfact : R = R ^ (1 / p) * R ^ (1 / q) := by
      rw [← Real.rpow_add hRpos, hpq.one_div_add_one_div, div_one, Real.rpow_one]
    nth_rw 1 [hfact] at hbound
    have hroot : R ^ (1 / p) ≤ S ^ (1 / p) :=
      le_of_mul_le_mul_right hbound (Real.rpow_pos_of_pos hRpos _)
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hR _) hroot hpq.nonneg
    simpa only [← Real.rpow_mul hR, ← Real.rpow_mul hS,
      one_div_mul_cancel hpq.ne_zero, Real.rpow_one] using h

/-- A coarse bound at every order above one. Its constant is sufficient to
prove finiteness after dividing channel-block divergences by block length. -/
theorem sandwichedQuasi_le_power_trace {p : ℝ} (hp : 1 < p)
    (ρ σ : L H) (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) (hdom : ρ ≤ c • σ) :
    (sandwichedQuasi p ρ σ).re ≤ c ^ p * (Tr σ).re := by
  let a : ℝ := (1 - p) / (2 * p)
  let S : L H := CFC.rpow σ a
  let X : L H := S * ρ * S
  let Y : L H := CFC.rpow σ (1 / p)
  have hp0 : 0 < p := by linarith
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hX : X.IsPositive := by
    have h := hρ.conj_adjoint S
    simpa only [hS.adjoint_eq] using h
  have hY : Y.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hexp : a + 1 + a = 1 / p := by dsimp [a]; field_simp; ring
  have ha1 : a + 1 ≠ 0 := by
    have heq : a + 1 = (p + 1) / (2 * p) := by dsimp [a]; field_simp; ring
    rw [heq]
    positivity
  have hSσS : S * σ * S = Y := by
    have hσpow : σ = CFC.rpow σ 1 :=
      (CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).mpr hσ)).symm
    calc
      S * σ * S = CFC.rpow σ a * CFC.rpow σ 1 * CFC.rpow σ a := by rw [← hσpow]
      _ = CFC.rpow σ (a + 1) * CFC.rpow σ a := by
        rw [operator_rpow_mul σ hσ a 1 ha1]
      _ = CFC.rpow σ (a + 1 + a) :=
        operator_rpow_mul σ hσ _ _ (by rw [hexp]; positivity)
      _ = Y := by rw [hexp]
  have hXY : X ≤ c • Y := by
    have h := hS.isSelfAdjoint.conjugate_le_conjugate hdom
    simpa only [mul_smul_comm, smul_mul_assoc, hSσS] using h
  have hcY : (c • Y).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (smul_nonneg hc CFC.rpow_nonneg)
  have hpow : CFC.rpow (c • Y) p = c ^ p • σ := by
    rw [operator_rpow_smul Y hY hc]
    congr 1
    dsimp only [Y]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg σ (1 / p) p (by positivity) hp0.le
      ((LinearMap.nonneg_iff_isPositive _).mpr hσ), one_div_mul_cancel hp0.ne',
      CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).mpr hσ)]
  have ht := trace_rpow_re_mono hp hX hcY hXY
  rw [hpow] at ht
  simpa only [sandwichedQuasi, a, S, X, LinearMap.map_smul_of_tower, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ht

end QuantumChannelContinuity


