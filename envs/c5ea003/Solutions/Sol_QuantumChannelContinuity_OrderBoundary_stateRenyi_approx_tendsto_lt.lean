-- Prove2me | solution 1 for QuantumChannelContinuity.OrderBoundary.stateRenyi_approx_tendsto_lt
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T03:43:18.444896+00:00
-- url     : https://prove2.me/submissions/1cb4fe07-f7fa-45ca-b591-96c0931bc098

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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
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
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderBoundary
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Theorems.Thm_SandwichedRenyiRelativeEntropy_ker_eq_bot_of_pdSetLM

section

/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/





/-!
# Sandwiched Rényi divergence on non-negative operators (Frank–Lieb extension)

This file extends the sandwiched Rényi divergence `D_α(ρ ‖ σ)` from the
positive-definite case to **non-negative** `ρ, σ ≥ 0`, following the convention
of Frank–Lieb (arXiv:1306.5358v3, §I.A).

## Main definitions

* `suppLE ρ σ` — support condition `ker σ ≤ ker ρ` (equivalent to `supp ρ ⊂ supp σ`).
* `sandwichedRenyiDivNN α ρ σ` — Frank–Lieb extension on `EReal`: equals
  `sandwichedRenyiDiv α ρ σ` when `α < 1` or `suppLE ρ σ`, and `⊤ : EReal`
  when `α > 1` and `¬ suppLE ρ σ`.

## Main theorem

* `sandwichedRenyiDivNN_monotone` — **Theorem 1** (Frank–Lieb): for any CPTP map
  `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any non-negative `ρ, σ`,
  `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`.

## Proof structure

The main theorem reduces via case analysis:

* `α > 1`, `¬ suppLE ρ σ`: RHS is `⊤`, trivial.
* otherwise: real-valued inequality, proven via the faithful-approximation
  `F_λ := (1−λ) E + λ · depolarizing` (faithful for `λ > 0`), the perturbed
  Theorem 1 for faithful channels (`sandwichedRenyiDiv_monotone_nonneg_perturbed`),
  and boundary continuity of `sandwichedRenyiDiv` as `ε → 0+`.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-! ### Support condition `suppLE` -/



/-- The support condition `suppLE ρ σ` holds trivially when `σ ∈ pdSetLM`. -/
private lemma suppLE_of_pdSetLM_right
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    suppLE ρ σ := by
  intro x hx
  have hker : LinearMap.ker σ = ⊥ := ker_eq_bot_of_pdSetLM hσ
  rw [hker, Submodule.mem_bot] at hx
  simp [hx]

/-! ### Frank–Lieb explicit formula -/



/-! ### Auxiliary spectral / order lemmas -/









/-! ### Support preservation under positive maps -/



/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/











/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

















/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/















/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/





























/-! ### Helpers for the `α < 1` main-theorem case -/











/-! ### Real-valued monotonicity (used in the main theorem) -/















/-! ### Main theorem: Theorem 1 for non-negative operators, general CPTP -/



/-! ### α = ∞ : max-relative entropy -/

section MaxRelEntropy

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]





















/-! ### α = ∞ : the order-theoretic characterization and the data-processing inequality

`maxRelEntropyNN` is *defined* via the explicit Frank–Lieb formula
`D_∞(ρ‖σ) = log ‖σ^{-1/2} ρ σ^{-1/2}‖` [arXiv:1306.5358]. Here we prove it equals the
order-theoretic form `log inf{λ ≥ 0 : ρ ≤ λ σ}` (`maxRelEntropyNN_eq_log_sInf`), and use
that characterization to prove the data-processing inequality (Theorem 1, `α = ∞`). -/





























end MaxRelEntropy

end SandwichedRenyiRelativeEntropy

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-! # Extending order inequalities from faithful to arbitrary density states -/
open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity
namespace OrderBoundary
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false












private theorem approx_pd (ρ : DensityState H) (l : ApproxParameter) :
    (approx ρ l).op ∈ pdSetLM :=
  faithfulApprox_pdSetLM (identity H) l.property.1 l.property.2 ρ.nonneg ρ.op_ne_zero

private theorem approx_tendsto (ρ : DensityState H) :
    Tendsto (fun l => (approx ρ l).op) approxFilter (𝓝 ρ.op) :=
  faithfulApprox_tendsto (identity H) ρ.op

private theorem stateRenyi_eq_coe_pd {p : ℝ} (hp : 0 < p)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi p ρ σ = ((sandwichedRenyiDiv p ρ.op σ.op / Real.log 2 : ℝ) : EReal) := by
  have hs := suppLE_of_pdSetLM_right ρ.op hσ
  have hQ := sandwichedQuasi_re_ne_zero_of_pdSetLM hp hρ hσ
  simp only [stateRenyi,sandwichedRenyiDivNN,hs,not_true_eq_false,and_false,hQ,
    or_self,↓reduceIte,toBits_coe]



private theorem quasi_approx_tendsto_lt {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (ρ σ : DensityState H) :
    Tendsto (fun l => (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re)
      approxFilter (𝓝 (sandwichedQuasi p ρ.op σ.op).re) := by
  have hpair : Tendsto
      (fun l : ApproxParameter => ((approx ρ l).op,(approx σ l).op)) approxFilter
      (𝓝[({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A})] (ρ.op,σ.op)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨(approx_tendsto ρ).prodMk_nhds (approx_tendsto σ),
      Filter.Eventually.of_forall (fun l => ⟨(approx ρ l).nonneg,(approx σ l).nonneg⟩)⟩
  have hc : Tendsto (fun v : L H × L H => (sandwichedQuasi p v.1 v.2).re)
      (𝓝[({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A})] (ρ.op,σ.op))
      (𝓝 (sandwichedQuasi p ρ.op σ.op).re) :=
    sandwichedQuasi_re_continuousOn_nonneg hp hp1 (ρ.op,σ.op) ⟨ρ.nonneg,σ.nonneg⟩
  have hh := hc.comp hpair
  exact hh

private theorem stateRenyi_approx_eq {p : ℝ} (hp : 0 < p)
    (ρ σ : DensityState H) (l : ApproxParameter) :
    stateRenyi p (approx ρ l) (approx σ l) =
      ((Real.log (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re *
        ((1 / (p - 1)) / Real.log 2) : ℝ) : EReal) := by
  rw [stateRenyi_eq_coe_pd hp _ _ (approx_pd ρ l) (approx_pd σ l)]
  simp only [sandwichedRenyiDiv,(approx ρ l).trace_one,Complex.one_re,div_one]
  congr 1
  ring

end OrderBoundary
end QuantumChannelContinuity

open QuantumChannelContinuity QuantumChannelContinuity.OrderBoundary
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open QuantumChannelContinuity QuantumChannelContinuity.OrderBoundary in
/-- Below one, faithful approximations converge even when the limiting states
are orthogonal: the logarithm then tends to minus infinity and the negative
Rényi coefficient sends it to plus infinity. -/
theorem solution {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ρ σ : DensityState H) :
    Tendsto (fun l => stateRenyi p (approx ρ l) (approx σ l)) approxFilter
      (𝓝 (stateRenyi p ρ σ)) := by
  have hQ := quasi_approx_tendsto_lt hp hp1.le ρ σ
  by_cases hz : (sandwichedQuasi p ρ.op σ.op).re = 0
  · have htarget : stateRenyi p ρ σ = ⊤ := by
      simp [stateRenyi,sandwichedRenyiDivNN,hp1,ρ.op_ne_zero,hz]
    rw [htarget]
    have hQpos (l : ApproxParameter) :
        0 < (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re := by
      exact sandwichedQuasi_pos_of_support hp _ _ (approx ρ l).nonneg (approx σ l).nonneg
        (suppLE_of_pdSetLM_right _ (approx_pd σ l)) (approx ρ l).op_ne_zero
    have hQwithin : Tendsto
        (fun l => (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re)
        approxFilter (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hz] using hQ,
        Filter.Eventually.of_forall hQpos⟩
    have hneg : (1 / (p - 1)) / Real.log 2 < 0 :=
      div_neg_of_neg_of_pos (one_div_neg.mpr (sub_neg.mpr hp1)) log_two_pos
    have htop := ((Real.tendsto_log_nhdsGT_zero.comp hQwithin).atBot_mul_const_of_neg hneg)
    apply (EReal.tendsto_coe_atTop.comp htop).congr'
    filter_upwards with l
    exact (stateRenyi_approx_eq hp ρ σ l).symm
  · have hlog := ((Real.continuousAt_log hz).tendsto.comp hQ).mul_const
      ((1 / (p - 1)) / Real.log 2)
    have htarget : stateRenyi p ρ σ =
        ((Real.log (sandwichedQuasi p ρ.op σ.op).re *
          ((1 / (p - 1)) / Real.log 2) : ℝ) : EReal) := by
      simp only [stateRenyi,sandwichedRenyiDivNN,not_lt.mpr hp1.le,false_and,
        hz,and_false,or_self,↓reduceIte,toBits_coe,sandwichedRenyiDiv,
        ρ.trace_one,Complex.one_re,div_one]
      congr 1
      ring
    rw [htarget]
    apply ((continuous_coe_real_ereal.tendsto _).comp hlog).congr'
    filter_upwards with l
    exact (stateRenyi_approx_eq hp ρ σ l).symm

end
