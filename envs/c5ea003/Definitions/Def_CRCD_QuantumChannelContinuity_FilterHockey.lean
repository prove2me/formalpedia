-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
-- name    : CRCD_QuantumChannelContinuity_FilterHockey
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:48:39.446919+00:00
-- url     : https://prove2.me/theorems/9b866b32-263f-41ca-b0ab-5c69745f78a8
-- title:
--   Hockey-stick slack attainment predicate
-- statement:
--   For completely positive trace-preserving maps $N,M:A\to B$ between nonzero finite-dimensional complex Hilbert spaces and a real $\gamma$, the predicate `HockeySlackAttainment` asserts that there is a completely positive superoperator $Q$ satisfying
--   $$
--   N\le_{\mathrm{CP}}\gamma M+Q,\qquad \operatorname{Re}\operatorname{Tr}Q(|a\rangle\langle a|)\le E_\gamma(N\Vert M)\|a\|^2\quad(a\in A).
--   $$
--   The scalar multiplication of $M$ is the complex-linear extension of the real number $\gamma$. This is an existence predicate, not an assumption-free assertion of attainment. The supporting filter theorem takes a proof of this predicate as an explicit premise and converts the slack into a controlled error for a fixed dilation.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FilterHockey.lean#L28-L71

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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
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
# The CP-slack interface for the hockey-stick filter

`HockeySlackAttainment` states the existence part of Gour equation (44) in
terms of actual completely positive maps and pure-input traces.  It is an
explicit proposition, proved unconditionally for nonnegative thresholds in
`SlackAttainment`. The theorem below composes it with the prescribed-dilation
operator construction in `FilterSlack`.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]

theorem cp_smul_nonneg {Φ : QuantumChannel.T A B}
    (hΦ : IsCompletelyPositive Φ) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsCompletelyPositive ((γ : ℂ) • Φ) := by
  let U : L B := (Real.sqrt γ : ℂ) • LinearMap.id
  have hU : LinearMap.adjoint U = U := by
    dsimp only [U]
    rw [map_smulₛₗ]
    simp
  have heq : (γ : ℂ) • Φ = (krausTerm U).comp Φ := by
    ext1 X
    change (γ : ℂ) • Φ X = U.comp ((Φ X).comp (LinearMap.adjoint U))
    rw [hU]
    ext1 x
    simp only [U, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_smul, smul_smul]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ]
  rw [heq]
  exact comp_isCompletelyPositive Φ (krausTerm U) hΦ (krausTerm_isCompletelyPositive U)

variable [Nontrivial A] [Nontrivial B]

/-- The exact SDP attainment assertion: a CP upper slack for `N - γ M`
whose trace effect is bounded by the stabilized testing optimum. -/
def HockeySlackAttainment (γ : ℝ) (N M : CPTP A B) : Prop :=
  ∃ Q : QuantumChannel.T A B,
    IsCompletelyPositive Q ∧
    CPLe N.toLinearMap ((γ : ℂ) • M.toLinearMap + Q) ∧
    ∀ a : A, (Tr (Q (outer_product a a))).re ≤ channelHockey γ N M * ‖a‖ ^ 2

/-- The manuscript's fixed-dilation hockey-stick filter, conditional only on
the exact slack-attainment assertion.  The Stinespring, ordered-CP,
environment alignment, square-root, and norm steps are all proved. -/
theorem fixed_dilation_hockey_filter_of_slack_attainment
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E) {γ : ℝ}
    (hγ : 0 ≤ γ) (hV : dilationChannel V = N.toLinearMap)
    (hattain : HockeySlackAttainment γ N M) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] E,
      CPLe (dilationChannel W) ((γ : ℂ) • M.toLinearMap) ∧
      ‖(V - W).toContinuousLinearMap‖ ≤ Real.sqrt (channelHockey γ N M) := by
  obtain ⟨Q, hQ, hdom, htrace⟩ := hattain
  exact fixed_dilation_filter_of_cp_slack V ((γ : ℂ) • M.toLinearMap) Q
    (channelHockey γ N M) (channelHockey_nonneg hγ N M)
    (cp_smul_nonneg ⟨M.toCompletelyPositiveMap, rfl⟩ hγ) hQ
    (by simpa only [hV] using hdom) htrace

end QuantumChannelContinuity


