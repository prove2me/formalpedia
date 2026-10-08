-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_StateDominationBounds
-- name    : CRCD_QuantumChannelContinuity_StateDominationBounds
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:36:51.194039+00:00
-- url     : https://prove2.me/theorems/67e74865-e055-45d6-bd5c-6c8074f8e11b
-- title:
--   State-divergence bounds for singular and faithful operator domination
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, if $\rho\ge0$ and $\rho\le c\sigma$ for an arbitrary real $c$, then $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. This support statement imposes no separate nonnegativity or invertibility premise on $\sigma$. For density states and $c>0$, every order $p>1$ satisfies the bit-valued coarse bound
--
--   $$
--   D_p(\rho\|\sigma)\le\frac p{p-1}\log_2c.
--   $$
--
--   For $c\ge1$, the relative entropy of density states is at most $\log_2c$.
--
--   The internal trace-normalized divergences use natural logarithms: for nonnegative $\rho,\sigma$ with $\rho\ne0$, $\rho\le c\sigma$, $c>0$, and $1<p\le2$, the normalized sandwiched divergence is at most $\ln c$. The normalized Umegaki divergence is likewise at most $\ln c$ for faithful positive-definite operators and $c>0$, and for arbitrary nonnegative operators with $\rho\ne0$ when $c\ge1$. The latter statement includes singular, noncommuting operators; normalization by trace and conversion from nats to bits are distinct conventions.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/StateDominationBounds.lean#L28-L113

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
# Uniform state-divergence bounds from operator domination

These results discharge finiteness and cap bounds. The proof of the Umegaki
bound passes through faithful perturbations and their proved boundary limit,
so it covers support-included singular, noncommuting states.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Domination implies support inclusion, with no invertibility assumption. -/
theorem suppLE_of_nonneg_le_smul {ρ σ : L H} (hρ : 0 ≤ ρ) {c : ℝ}
    (hdom : ρ ≤ c • σ) : suppLE ρ σ := by
  intro x hx
  apply nonneg_eq_zero_of_le_of_apply_eq_zero hρ hdom
  change c • σ x = 0
  rw [show σ x = 0 from hx, smul_zero]

/-- Above one, the coarse all-order trace bound gives an explicit finite
upper bound for the normalized state divergence. -/
theorem stateRenyi_le_coarse_log_of_le {p c : ℝ} (hp : 1 < p) (hc : 0 < c)
    (ρ σ : DensityState H) (hdom : ρ.op ≤ c • σ.op) :
    stateRenyi p ρ σ ≤ ((p / (p - 1)) * Real.logb 2 c : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hs := suppLE_of_nonneg_le_smul ρ.nonneg hdom
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ.op σ.op ρ.nonneg σ.nonneg hs ρ.op_ne_zero
  have hbound := sandwichedQuasi_le_power_trace hp ρ.op σ.op
    ((LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg)
    ((LinearMap.nonneg_iff_isPositive _).mp σ.nonneg) hc.le hdom
  rw [σ.trace_one, Complex.one_re, mul_one] at hbound
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hQ hbound
  rw [Real.logb_rpow_eq_mul_logb_of_pos hc] at hlog
  rw [stateRenyi_eq_formula hp ρ σ hs, EReal.coe_le_coe_iff]
  have h := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (sub_pos.mpr hp).le)
  convert h using 1 <;> ring

/-- The sharp near-one bound for unnormalized positive operators. -/
theorem sandwichedRenyiDiv_le_log_of_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hc : 0 < c) {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hdom : ρ ≤ c • σ) : sandwichedRenyiDiv p ρ σ ≤ Real.log c := by
  have hp0 : 0 < p := by linarith
  have ht : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  have hs := suppLE_of_nonneg_le_smul hρ hdom
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ σ hρ hσ hs hρ0
  have hbound := sandwichedQuasi_le_of_le hp hp2 ρ σ
    ((LinearMap.nonneg_iff_isPositive _).mp hρ)
    ((LinearMap.nonneg_iff_isPositive _).mp hσ) hc.le hdom
  have hquot : (sandwichedQuasi p ρ σ).re / (Tr ρ).re ≤ c ^ (p - 1) :=
    (div_le_iff₀ ht).mpr hbound
  have hlog := Real.log_le_log (div_pos hQ ht) hquot
  rw [Real.log_rpow hc] at hlog
  have h := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (sub_pos.mpr hp).le)
  change (1 / (p - 1)) * Real.log ((sandwichedQuasi p ρ σ).re / (Tr ρ).re) ≤ _
  convert h using 1
  field_simp [ne_of_gt (sub_pos.mpr hp)]

/-- The Umegaki domination bound for faithful, not necessarily normalized operators. -/
theorem umegakiNorm_le_log_of_le_pd {c : ℝ} (hc : 0 < c)
    {ρ σ : L H} (hρ : ρ ∈ pdSetLM) (hσ : σ ∈ pdSetLM)
    (hdom : ρ ≤ c • σ) : umegakiNorm ρ σ ≤ Real.log c := by
  apply le_of_tendsto (sandwichedRenyiDiv_tendsto_umegaki hρ hσ)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds]
    with p hp hp2
  exact sandwichedRenyiDiv_le_log_of_le hp hp2.le hc
    (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
    (by intro hz; have h := trace_re_pos_of_pdSetLM hρ; simp [hz] at h) hdom

/-- The same Umegaki bound for arbitrary support-included nonnegative
operators. Faithful perturbations preserve the domination constant `c≥1`. -/
theorem umegakiNorm_le_log_of_le {c : ℝ} (hc : 1 ≤ c)
    {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hdom : ρ ≤ c • σ) : umegakiNorm ρ σ ≤ Real.log c := by
  have hs := suppLE_of_nonneg_le_smul hρ hdom
  apply le_of_tendsto (tendsto_umegakiNorm_perturb hρ hσ hρ0 hs)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  apply umegakiNorm_le_log_of_le_pd (zero_lt_one.trans_le hc)
    (pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hεpos))
    (pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hεpos))
  have hεone : (ε : ℂ) • (1 : L H) ≤ c • ((ε : ℂ) • (1 : L H)) := by
    have hnn : 0 ≤ (ε : ℂ) • (1 : L H) :=
      smul_nonneg (by exact_mod_cast hεpos.le) zero_le_one
    simpa only [one_smul] using smul_le_smul_of_nonneg_right hc hnn
  simpa only [smul_add] using add_le_add hdom hεone

/-- Finite max-relative domination bounds the actual support-aware state
relative entropy in bits, including singular states. -/
theorem stateRelative_le_log_of_le {c : ℝ} (hc : 1 ≤ c)
    (ρ σ : DensityState H) (hdom : ρ.op ≤ c • σ.op) :
    stateRelative ρ σ ≤ (Real.logb 2 c : ℝ) := by
  have hs := suppLE_of_nonneg_le_smul ρ.nonneg hdom
  have h := umegakiNorm_le_log_of_le hc ρ.nonneg σ.nonneg ρ.op_ne_zero hdom
  have hb := toBits_mono (EReal.coe_le_coe_iff.mpr h)
  simpa only [stateRelative, umegakiRelEntropyNN, hs, ↓reduceIte, toBits_coe,
    Real.logb] using hb

end QuantumChannelContinuity


