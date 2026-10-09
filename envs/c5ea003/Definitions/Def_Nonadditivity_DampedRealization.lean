-- Prove2me | Definitions.Def_Nonadditivity_DampedRealization
-- name    : Nonadditivity_DampedRealization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:48:40.995976+00:00
-- url     : https://prove2.me/theorems/b8656038-dca0-4ccc-bcf2-e9e49b2e8963
-- title:
--   Choosing a moment order before the input dimension
-- statement:
--   Fix a finite nonempty output space $O$, real numbers $a>1$, $c>0$, and $\eta>0$. There is an integer $p\ge1$, chosen before the finite input space or Kraus channel, with the following property. If a channel $T:I\to O$ satisfies
--   $$\frac{\operatorname{Re}\operatorname{Tr}((T^*(A))^{2p})}{|I|}\le c^{2p}$$
--   for every traceless Hermitian $A$ with $\|A\|_{\rm HS}=1$, then there are input matrices $F,G$ with $F=F^*$, $I-F^2\succeq0$, $GF=I$, and
--   $$\|T_F^*(A)\|\le ac\|A\|_{\rm HS},\qquad \frac{\operatorname{Re}\operatorname{Tr}(I-F^2)}{|I|}<\eta.$$
--   The norm bound holds for every traceless Hermitian output matrix, and $T_F$ is the genuine damped Kraus channel. This result turns an assumed normalized moment certificate into invertible damping with arbitrarily small normalized loss.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DampedRealization.lean#L19-L72

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_DampingNet
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_SpectralDamping
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Star.Unitary

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! Deterministic realization of a channel norm certificate from finite even moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Nonadditivity.DampedRealization
open Channels Channels.KrausChannel AdjointPurity FiniteRealization
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {ο : Type} [Fintype ο] [DecidableEq ο] [Nonempty ο]

/-- The moment order is selected before the finite input space or channel.
Every model with these moments yields an actual invertible damping with the
prescribed certificate and arbitrarily small normalized discarded mass. -/
theorem exists_moment_order {a c η : ℝ} (ha : 1 < a) (hc : 0 < c) (hη : 0 < η) :
    ∃ p : ℕ, 1 ≤ p ∧
      ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
      (T : KrausChannel ι ο κ),
      (∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 → hsLength A=1 →
        ((T.adjointMap A)^(2*p)).trace.re / (Fintype.card ι : ℝ) ≤ c^(2*p)) →
      ∃ F G : Matrix ι ι ℂ, ∃ hF : F.IsHermitian, ∃ hres : (1-F*F).PosSemidef,
        G*F=1 ∧
        (∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
          ‖(DampedChannel.damped T F hF hres).adjointMap A‖ ≤ a*c*hsLength A) ∧
        (1-F*F).trace.re / (Fintype.card ι : ℝ) < η := by
  classical
  let δ : ℝ := (a-1)/(a+1)
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  let L : ℝ := (1+δ)*c
  have hL : 0 < L := mul_pos (by linarith) hc
  have hcL : c < L := by dsimp [L]; nlinarith
  have hr0 : 0 ≤ c/L := div_nonneg hc.le hL.le
  have hr1 : c/L < 1 := (div_lt_one hL).mpr hcL
  obtain ⟨tests, hunit, hnet⟩ := exists_unitSphereNet (E := ObservableSpace ο) hδ
  obtain ⟨p, hp, hsmall⟩ := DampingNet.exists_even_moment_small hr0 hr1 tests.card hη
  refine ⟨p, hp, ?_⟩
  intro ι κ _ _ _ _ T hmom
  let X : tests → Matrix ι ι ℂ := fun y => T.adjointMap (observableMatrix y.val)
  have hX (y : tests) : (X y).IsHermitian :=
    T.adjointMap_isHermitian _ (observableMatrix_isHermitian y.val)
  obtain ⟨F,G,hF,hres,hGF,hbound,hloss⟩ := SpectralDamping.exists_damping X hX L hL p hp
  refine ⟨F,G,hF,hres,hGF,?_,?_⟩
  · apply DampingNet.damped_certificate T F hF hres ha hc.le hnet
    intro y hy
    exact hbound ⟨y,hy⟩
  · have hdim : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    have hterm (y : tests) :
        L⁻¹^(2*p) * (X y^(2*p)).trace.re / (Fintype.card ι : ℝ) ≤ (c/L)^(2*p) := by
      have h := hmom (observableMatrix y.val) (observableMatrix_isHermitian _)
        (observableMatrix_trace_zero _)
        (by rw [← observable_norm_eq_hsLength]; exact hunit y.val y.property)
      have h' := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hL.le) (2*p))
      convert h' using 1 <;> dsimp only [X]
      · ring
      · rw [div_eq_mul_inv, mul_pow]; ring
    calc
      (1-F*F).trace.re / (Fintype.card ι : ℝ) ≤
          (2 * ∑ y : tests, L⁻¹^(2*p) * (X y^(2*p)).trace.re) /
            (Fintype.card ι : ℝ) := div_le_div_of_nonneg_right hloss hdim.le
      _ = 2 * ∑ y : tests, L⁻¹^(2*p) * (X y^(2*p)).trace.re /
            (Fintype.card ι : ℝ) := by rw [← Finset.sum_div]; ring
      _ ≤ 2 * ∑ _y : tests, (c/L)^(2*p) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => hterm y)) (by norm_num)
      _ = 2 * (tests.card : ℝ) * (c/L)^(2*p) := by simp; ring
      _ < η := hsmall

end Nonadditivity.DampedRealization


