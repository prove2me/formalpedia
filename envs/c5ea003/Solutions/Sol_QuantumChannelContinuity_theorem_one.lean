-- Prove2me | solution 1 for QuantumChannelContinuity.theorem_one
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:30:05.907816+00:00
-- url     : https://prove2.me/submissions/0b8dd939-9a16-4087-837c-b8ae87d6ce12

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
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Slope
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
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic
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
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelDominationBounds
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelProducts
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
import Definitions.Def_CRCD_QuantumChannelContinuity_ConcreteMain
import Definitions.Def_CRCD_QuantumChannelContinuity_ContinuityAssembly
import Definitions.Def_CRCD_QuantumChannelContinuity_DilationExistence
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_FiniteInfinite
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_PowerRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_QuantumMain
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationIdentities
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationSup
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizedExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPPartialTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackAttainment
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTester
import Definitions.Def_CRCD_QuantumChannelContinuity_SlackTraceBound
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateDominationBounds
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderBoundary
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderDuality
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderInterpolation
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderRenyi
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceFilter
import Definitions.Def_CRCD_QuantumChannelContinuity_TracePowerBounds
import Theorems.Thm_ChannelContinuity_FiniteAnalyticInputs_threshold_le_of_eventual_sqrt_bound
import Theorems.Thm_ChannelContinuity_eventual_sqrt_bound_of_weak_testing
import Theorems.Thm_QuantumChannelContinuity_OrderBoundary_sandwichedRenyiDiv_tendsto_faithful
import Theorems.Thm_QuantumChannelContinuity_OrderBoundary_stateRenyi_approx_tendsto_lt
import Theorems.Thm_QuantumChannelContinuity_regularizedRenyi_tendsto_one_left_of_mono
import Theorems.Thm_QuantumChannelContinuity_theorem_one_of_regularizedRelative_top
import Theorems.Thm_QuantumChannelContinuity_weightedSchattenLog_convex
import Theorems.Thm_SandwichedRenyiRelativeEntropy_ker_eq_bot_of_pdSetLM

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/









/-!
# The scalar threshold argument

This file formalizes the final real-analysis step in the proof of Theorem 1.
The two-term inequality is the manuscript's equation `eq:contradiction`.
All limits here are proved in Lean; quantum-information input is not postulated
as an axiom and appears explicitly as hypotheses where needed.
-/

open Filter Set
open scoped Topology

namespace ChannelContinuity











/-- A threshold below every rate above `d`, and bounded below by `d`, equals `d`.
This is the last order-theoretic step of the proof. -/
private theorem threshold_eq_of_forall_gt {d dPlus : ℝ} (hlower : d ≤ dPlus)
    (hupper : ∀ r : ℝ, d < r → dPlus ≤ r) : dPlus = d := by
  apply le_antisymm _ hlower
  by_contra h
  have hgap : d < dPlus := lt_of_not_ge h
  have := hupper ((d + dPlus) / 2) (by linarith)
  linarith



/-- A monotone real-valued order divergence converges from the right to its
infimum. This includes the bounded finite-max-relative-entropy case. -/
private theorem tendsto_right_to_infimum {f : ℝ → ℝ} {d : ℝ}
    (hmono : MonotoneOn f (Ioi 1)) (hlower : ∀ a : ℝ, 1 < a → d ≤ f a) :
    Tendsto f (𝓝[>] 1) (𝓝 (sInf (f '' Ioi 1))) := by
  apply hmono.tendsto_nhdsGT
  refine ⟨d, ?_⟩
  rintro y ⟨a, ha, rfl⟩
  exact hlower a ha

/-- Right continuity follows after identification of the infimum threshold. -/
private theorem tendsto_right_of_threshold_eq {f : ℝ → ℝ} {d : ℝ}
    (hmono : MonotoneOn f (Ioi 1)) (hlower : ∀ a : ℝ, 1 < a → d ≤ f a)
    (hthreshold : sInf (f '' Ioi 1) = d) :
    Tendsto f (𝓝[>] 1) (𝓝 d) := by
  simpa [hthreshold] using tendsto_right_to_infimum hmono hlower

/-- A lower bound valid at every order also bounds the finite right threshold. -/
private theorem le_infimum_of_order_bounds {f : ℝ → ℝ} {d : ℝ}
    (hlower : ∀ a : ℝ, 1 < a → d ≤ f a) :
    d ≤ sInf (f '' Ioi 1) := by
  apply le_csInf
  · exact ⟨f 2, 2, by norm_num, rfl⟩
  · rintro y ⟨a, ha, rfl⟩
    exact hlower a ha



end ChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/










/-!
# Scalar limit argument for Theorem 1

The successive limit passages, testing-threshold argument, and left/right
assembly are proved. `FiniteAnalyticInputs` records the scalar estimates needed
for the finite right-limit argument; its raw Schatten estimate is normalized
here. `QuantumChannelContinuity.QuantumMain` derives that estimate from the
proved operator bounds, and `QuantumChannelContinuity.ContinuityAssembly`
constructs the input record for concrete channels in the finite branch.
`QuantumChannelContinuity.Main` combines the finite and infinite cases with
the proved state-order facts to export the unconditional channel theorem.
-/

open Filter Set
open scoped Topology ENNReal

namespace ChannelContinuity









/-- The weak testing estimate supplies an eventual error below one at every
rate above `d`, so the finite thresholds coincide. -/
private theorem FiniteAnalyticInputs.threshold_eq (h : FiniteAnalyticInputs) :
    sInf (h.renyi '' Ioi 1) = h.d := by
  apply threshold_eq_of_forall_gt (le_infimum_of_order_bounds h.relative_le_renyi)
  intro r hr
  have hrpos : 0 < r := lt_of_le_of_lt h.d_nonneg hr
  obtain ⟨B, _, hBlt, hBevent⟩ := eventual_sqrt_bound_of_weak_testing
    h.d_nonneg hr (h.weak_testing r hrpos)
  exact h.threshold_le_of_eventual_sqrt_bound hrpos.le hBlt hBevent

/-- The complete finite right-limit argument from the stated quantum bridge. -/
private theorem FiniteAnalyticInputs.right_continuity (h : FiniteAnalyticInputs) :
    Tendsto h.renyi (𝓝[>] (1 : ℝ)) (𝓝 h.d) :=
  tendsto_right_of_threshold_eq h.order_mono h.relative_le_renyi h.threshold_eq



end ChannelContinuity

end


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





/-- The concrete block-supremum Rényi divergence is right-continuous at one
once the explicitly listed residual finite-case inputs are proved. -/
private theorem regularized_right_continuity_of_remaining {N M : CPTP H K}
    (h : RemainingFiniteInputs N M) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[>] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h.analytic.right_continuity
  change Tendsto (fun α => ENNReal.ofReal ((regularizedRenyi α N M).toReal))
    (𝓝[>] (1 : ℝ)) (𝓝 (ENNReal.ofReal ((regularizedRelative N M).toReal))) at hlim
  rw [ENNReal.ofReal_toReal h.relative_finite] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact ENNReal.ofReal_toReal (h.renyi_finite α hα)

















end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Intermediate continuity interface with the filter–Schatten estimate discharged

This modular interface lists state/order facts, exact CP-slack attainment,
a block CP cap, and scaling under channel powers. The later
`ContinuityAssembly.lean` constructs these inputs from state-order
monotonicity. The regularized three-piece Schatten estimate is derived here.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]











/-- Concrete right continuity, with no assumed Schatten or filtering estimate. -/
private theorem regularized_right_continuity_from_quantum_inputs {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[>] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) :=
  regularized_right_continuity_of_remaining h.toRemaining


end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Assembly from order monotonicity

This intermediate module isolates order monotonicity as the final state-level
input. All state limits, support cases, CP caps, exact slack attainment, and
regularization identities are supplied by the preceding concrete proofs.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]











/-- All finite and infinite cases assembled, with only pointwise state-order
monotonicity left to instantiate in the final module. -/
private theorem theorem_one_of_input_order (N M : CPTP H K)
    (hleft : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1))
    (hright : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1)) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  by_cases hfin : regularizedRelative N M = ⊤
  · exact theorem_one_of_regularizedRelative_top N M hfin
  · rw [← nhdsLT_sup_nhdsGT]
    exact (regularizedRenyi_tendsto_one_left_of_mono N M hleft).sup
      (regularized_right_continuity_from_quantum_inputs
        (quantumThresholdInputs_of_mono N M hfin hright))

end QuantumChannelContinuity

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



private theorem stateRenyi_eq_coe_pd {p : ℝ} (hp : 0 < p)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi p ρ σ = ((sandwichedRenyiDiv p ρ.op σ.op / Real.log 2 : ℝ) : EReal) := by
  have hs := suppLE_of_pdSetLM_right ρ.op hσ
  have hQ := sandwichedQuasi_re_ne_zero_of_pdSetLM hp hρ hσ
  simp only [stateRenyi,sandwichedRenyiDivNN,hs,not_true_eq_false,and_false,hQ,
    or_self,↓reduceIte,toBits_coe]

private theorem stateRenyi_approx_tendsto_gt {p : ℝ} (hp : 1 < p)
    (ρ σ : DensityState H) (hs : suppLE ρ.op σ.op) :
    Tendsto (fun l => stateRenyi p (approx ρ l) (approx σ l)) approxFilter
      (𝓝 (stateRenyi p ρ σ)) := by
  have hd := sandwichedRenyiDiv_tendsto_faithful (identity H) hp
    ρ.nonneg σ.nonneg σ.op_ne_zero ρ.op_ne_zero hs
  have hb := (continuous_coe_real_ereal.tendsto _).comp (hd.div_const (Real.log 2))
  have htarget : stateRenyi p ρ σ =
      ((sandwichedRenyiDiv p ρ.op σ.op / Real.log 2 : ℝ) : EReal) := by
    simp only [stateRenyi,sandwichedRenyiDivNN,not_lt.mpr hp.le,false_and,
      hs,not_true_eq_false,and_false,or_self,↓reduceIte,toBits_coe]
  rw [htarget]
  apply hb.congr'
  filter_upwards with l
  exact (stateRenyi_eq_coe_pd (by linarith) _ _ (approx_pd ρ l) (approx_pd σ l)).symm







end OrderBoundary

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000

/-- A proved transfer principle: faithful order monotonicity above one
extends to all density states, including support mismatch. -/
private theorem stateRenyi_le_of_faithful_gt {α β : ℝ} (hα : 1 < α) (hαβ : α ≤ β)
    (hfaithful : ∀ (ρ σ : DensityState H), ρ.op ∈ pdSetLM → σ.op ∈ pdSetLM →
      stateRenyi α ρ σ ≤ stateRenyi β ρ σ) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  by_cases hs : suppLE ρ.op σ.op
  · apply le_of_tendsto (OrderBoundary.stateRenyi_approx_tendsto_gt hα ρ σ hs)
    filter_upwards with l
    exact (hfaithful _ _ (OrderBoundary.approx_pd ρ l) (OrderBoundary.approx_pd σ l)).trans
      (stateRenyi_dataProcessing (OrderBoundary.approxChannel H l)
        (by linarith) (by linarith) ρ σ)
  · rw [stateRenyi_eq_top_of_not_support (hα.trans_le hαβ) ρ σ hs]
    exact le_top

/-- The same transfer below one handles zero overlap by actual extended-real
continuity, so it also permits a target order above one. -/
private theorem stateRenyi_le_of_faithful_lt {α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : (1 : ℝ) / 2 ≤ β) (hβ1 : β ≠ 1)
    (hfaithful : ∀ (ρ σ : DensityState H), ρ.op ∈ pdSetLM → σ.op ∈ pdSetLM →
      stateRenyi α ρ σ ≤ stateRenyi β ρ σ) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  apply le_of_tendsto (OrderBoundary.stateRenyi_approx_tendsto_lt hα hα1 ρ σ)
  filter_upwards with l
  exact (hfaithful _ _ (OrderBoundary.approx_pd ρ l) (OrderBoundary.approx_pd σ l)).trans
    (stateRenyi_dataProcessing (OrderBoundary.approxChannel H l) hβ hβ1 ρ σ)

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-! # Faithful polar witnesses for Schatten duality -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private theorem star_mul_self_strictlyPositive {C : L H} (hC : IsUnit C) :
    IsStrictlyPositive (star C * C) :=
  ⟨star_mul_self_nonneg _, hC.star.mul hC⟩







private theorem schattenWeight_pos {C : L H} (hC : IsUnit C) (p : ℝ) :
    0 < schattenWeight C p := by
  have hp : IsStrictlyPositive (CFC.rpow (star C * C) (p / 2)) :=
    IsStrictlyPositive.rpow (star C * C) (p / 2) (star_mul_self_strictlyPositive hC)
  exact trace_re_pos_of_ne_zero hp.nonneg hp.isUnit.ne_zero







end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-! # Scalar conversion from interpolation convexity to Rényi order -/

open Set
namespace QuantumChannelContinuity

private theorem reciprocal_order_mem {α : ℝ} (hα : 1 / 2 < α) :
    1 / (2 * α) ∈ Ioo (0 : ℝ) 1 := by
  have hα0 : 0 < 2 * α := by linarith
  exact ⟨one_div_pos.mpr hα0, (div_lt_one hα0).mpr (by linarith)⟩

private theorem reciprocal_order_ne_half {α : ℝ} (hα : 1 / 2 < α) (hα1 : α ≠ 1) :
    1 / (2 * α) ≠ (1 / 2 : ℝ) := by
  have hα0 : 0 < 2 * α := by linarith
  intro h
  have hh := (div_eq_iff hα0.ne').mp h
  apply hα1
  linarith

/-- Increasing Rényi order reverses the reciprocal interpolation parameter.
Convex secant slopes therefore give the required monotonicity on both sides
of one (and across it), with no endpoint differentiability assumption. -/
private theorem renyi_order_of_convex_log_norm {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Ioo 0 1) g) (hcenter : g (1 / 2) = 0)
    {α β : ℝ} (hα : 1 / 2 < α) (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hαβ : α ≤ β) :
    -g (1 / (2 * α)) / (1 / (2 * α) - 1 / 2) ≤
      -g (1 / (2 * β)) / (1 / (2 * β) - 1 / 2) := by
  have hβ : 1 / 2 < β := hα.trans_le hαβ
  have hparam : 1 / (2 * β) ≤ 1 / (2 * α) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hs := hg.secant_mono (a := (1 / 2 : ℝ)) (by norm_num)
    (reciprocal_order_mem hβ) (reciprocal_order_mem hα)
    (reciprocal_order_ne_half hβ hβ1) (reciprocal_order_ne_half hα hα1) hparam
  simpa only [hcenter, sub_zero, neg_div] using neg_le_neg hs

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-! # From weighted Schatten interpolation to Rényi order monotonicity

The logarithm of the weighted Schatten norm is convex in reciprocal order.
Its value at reciprocal order one half is zero, so its secant slopes give
monotonicity of the actual sandwiched Rényi divergence on faithful states.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false



private theorem sqrt_weighted_density (ρ σ : L H) (hρ : IsStrictlyPositive ρ) (t : ℝ) :
    star (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ t) *
      (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ t) = CFC.rpow σ t * ρ * CFC.rpow σ t := by
  have hstar (X : L H) (a : ℝ) : star (CFC.rpow X a) = CFC.rpow X a :=
    CFC.rpow_nonneg.isSelfAdjoint.star_eq
  have hsq : CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow ρ (1 / 2 : ℝ) = ρ := by
    calc
      _ = CFC.rpow ρ ((1 / 2 : ℝ) + 1 / 2) := (CFC.rpow_add hρ.isUnit).symm
      _ = ρ := by norm_num only; exact CFC.rpow_one _ hρ.nonneg
  rw [star_mul, hstar, hstar, mul_assoc, ← mul_assoc (CFC.rpow ρ (1 / 2 : ℝ)), hsq, mul_assoc]

private theorem sqrt_weighted_schattenWeight (ρ σ : L H) (hρ : IsStrictlyPositive ρ)
    {α : ℝ} (hα : α ≠ 0) :
    schattenWeight (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (1 / (2 * α) - 1 / 2))
      (2 * α) = (sandwichedQuasi α ρ σ).re := by
  unfold schattenWeight sandwichedQuasi
  rw [sqrt_weighted_density ρ σ hρ]
  have hexp : 1 / (2 * α) - 1 / 2 = (1 - α) / (2 * α) := by field_simp
  rw [hexp]
  congr 3
  ring

private theorem weightedSchattenLog_eq_log_quasi (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    {α : ℝ} (hα : α ≠ 0) :
    weightedSchattenLog ρ σ (1 / (2 * α)) =
      (1 / (2 * α)) * Real.log (sandwichedQuasi α ρ σ).re := by
  have hC : IsUnit (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (1 / (2 * α) - 1 / 2)) :=
    (IsStrictlyPositive.rpow ρ (1 / 2 : ℝ) hρ).isUnit.mul (IsStrictlyPositive.rpow σ (1 / (2 * α) - 1 / 2) hσ).isUnit
  unfold weightedSchattenLog schattenNorm
  rw [one_div_one_div, Real.log_rpow (schattenWeight_pos hC _),
    sqrt_weighted_schattenWeight ρ σ hρ hα]

private theorem weightedSchattenLog_half (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) (hTr : (Tr ρ).re = 1) :
    weightedSchattenLog ρ σ (1 / 2) = 0 := by
  have hweight : schattenWeight
      (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ ((1 / 2 : ℝ) - 1 / 2)) (1 / (1 / 2 : ℝ)) = 1 := by
    unfold schattenWeight
    rw [sqrt_weighted_density ρ σ hρ]
    norm_num only
    simp only [CFC.rpow_eq_pow, CFC.rpow_zero σ hσ.nonneg, one_mul, mul_one,
      CFC.rpow_one ρ hρ.nonneg, hTr]
  unfold weightedSchattenLog schattenNorm
  rw [hweight, Real.one_rpow, Real.log_one]



/-- The actual base-two divergence is the negative secant slope of the
logarithmic weighted norm through reciprocal order one half. -/
private theorem stateRenyi_eq_weighted_secant {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi α ρ σ =
      (((-weightedSchattenLog ρ.op σ.op (1 / (2 * α)) /
        (1 / (2 * α) - 1 / 2)) / Real.log 2 : ℝ) : EReal) := by
  rw [OrderBoundary.stateRenyi_eq_coe_pd hα ρ σ hρ hσ,
    weightedSchattenLog_eq_log_quasi ρ.op σ.op
      (isStrictlyPositive_of_pdSetLM hρ) (isStrictlyPositive_of_pdSetLM hσ) hα.ne']
  simp only [sandwichedRenyiDiv, ρ.trace_one, Complex.one_re, div_one]
  congr 1
  have hαsub : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
  have h1sub : 1 - α ≠ 0 := sub_ne_zero.mpr hα1.symm
  field_simp [hα.ne', hαsub, h1sub]
  ring

/-- Faithful state Rényi divergence is monotone in its order, both above
and below one and also across one. All interpolation inputs are proved. -/
private theorem stateRenyi_le_of_faithful {α β : ℝ} (hα : 1 / 2 < α)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≤ β)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  have hρp := isStrictlyPositive_of_pdSetLM hρ
  have hσp := isStrictlyPositive_of_pdSetLM hσ
  have h := renyi_order_of_convex_log_norm
    (weightedSchattenLog_convex ρ.op σ.op hρp hσp)
    (weightedSchattenLog_half ρ.op σ.op hρp hσp (by rw [ρ.trace_one]; rfl))
    hα hα1 hβ1 hαβ
  rw [stateRenyi_eq_weighted_secant (by linarith) hα1 ρ σ hρ hσ,
    stateRenyi_eq_weighted_secant (by linarith) hβ1 ρ σ hρ hσ, EReal.coe_le_coe_iff]
  exact div_le_div_of_nonneg_right h log_two_pos.le

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Unconditional Rényi order monotonicity

Complex interpolation proves the faithful inequality. The proved density
approximation and data-processing argument extends it to singular states,
including the support-mismatch and zero-overlap infinity conventions.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
variable {H : Type} [Qudit H] [Nontrivial H]

/-- Rényi divergence is increasing with its order, across both sides of one.
The endpoints exclude one itself, where the expression is defined separately. -/
private theorem stateRenyi_le_of_order {α β : ℝ} (hα : (1 : ℝ) / 2 < α)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≤ β) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  have hf : ∀ (τ ω : DensityState H), τ.op ∈ pdSetLM → ω.op ∈ pdSetLM →
      stateRenyi α τ ω ≤ stateRenyi β τ ω :=
    fun τ ω hτ hω => stateRenyi_le_of_faithful hα hα1 hβ1 hαβ τ ω hτ hω
  by_cases hl : α < 1
  · exact stateRenyi_le_of_faithful_lt (by linarith) hl (by linarith) hβ1 hf ρ σ
  · exact stateRenyi_le_of_faithful_gt (by rcases lt_or_gt_of_ne hα1 with h | h <;> linarith)
      hαβ hf ρ σ

/-- Monotonicity below one for arbitrary density states. -/
private theorem stateRenyi_monotoneOn_left (ρ σ : DensityState H) :
    MonotoneOn (fun α => stateRenyi α ρ σ) (Ioo (1 / 2) 1) := by
  intro α hα β hβ hαβ
  exact stateRenyi_le_of_order hα.1 hα.2.ne hβ.2.ne hαβ ρ σ

/-- Monotonicity above one for arbitrary density states. -/
private theorem stateRenyi_monotoneOn_right (ρ σ : DensityState H) :
    MonotoneOn (fun α => stateRenyi α ρ σ) (Ioi 1) := by
  intro α hα β hβ hαβ
  exact stateRenyi_le_of_order (by change 1 < α at hα; linarith)
    (ne_of_gt hα) (ne_of_gt hβ) hαβ ρ σ





end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Theorem 1 for finite-dimensional quantum channels

The two-sided order-one limit holds for every pair of CPTP channels between
nonzero finite-dimensional complex Hilbert spaces. All state, order, support,
slack-attainment, Stinespring/filter, Schatten, and regularization ingredients
are proved. There are no additional quantum-information premises.

The regularized quantities use positive-block suprema; the theorems
`blockRenyi_tendsto_regularized` and `blockRelative_tendsto_regularized`
identify these with the manuscript's normalized block limits, including infinity.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

private theorem inputRenyi_monotoneOn_left (N M : CPTP H K) (i : BlockInput H) :
    MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1) := by
  intro α hα β hβ hαβ
  exact ENNReal.div_le_div_right (EReal.toENNReal_le_toENNReal
    (stateRenyi_monotoneOn_left
      (amplifiedOutput (channelPower N i.1.val) i.2.density)
      (amplifiedOutput (channelPower M i.1.val) i.2.density) hα hβ hαβ)) _

private theorem inputRenyi_monotoneOn_right (N M : CPTP H K) (i : BlockInput H) :
    MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1) := by
  intro α hα β hβ hαβ
  exact ENNReal.div_le_div_right (EReal.toENNReal_le_toENNReal
    (stateRenyi_monotoneOn_right
      (amplifiedOutput (channelPower N i.1.val) i.2.density)
      (amplifiedOutput (channelPower M i.1.val) i.2.density) hα hβ hαβ)) _


end QuantumChannelContinuity

open QuantumChannelContinuity
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
open QuantumChannelContinuity in
/-- Theorem 1: unconditional two-sided continuity at order one for actual
regularized, stabilized sandwiched Rényi channel divergence, in bits.
The value may be finite or infinite; no support or finiteness hypothesis is needed. -/
theorem solution (N M : CPTP H K) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) :=
  theorem_one_of_input_order N M
    (inputRenyi_monotoneOn_left N M) (inputRenyi_monotoneOn_right N M)

end
