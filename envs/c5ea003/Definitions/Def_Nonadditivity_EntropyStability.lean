-- Prove2me | Definitions.Def_Nonadditivity_EntropyStability
-- name    : Nonadditivity_EntropyStability
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:48:11.044119+00:00
-- url     : https://prove2.me/theorems/e3a3d618-0bab-4c6e-ab9e-c4d4979fd177
-- title:
--   Bell-output entropy stability under small normalized filter loss
-- statement:
--   Fix a finite nonempty output space $O$ and an entropy error $\eta>0$. There is a threshold $\varepsilon>0$, depending on $O$ and $\eta$, such that every finite Kraus channel $T:I\to O$ and Hermitian input filter $F$ with $I-F^2\succeq0$ obey
--   $$\ell(F)<\varepsilon\ \Longrightarrow\ S(\operatorname{Bell}(T_F))\le S(\operatorname{Bell}(T))+\eta,\qquad \ell(F)=\frac{\operatorname{Re}\operatorname{Tr}(I-F^2)}{|I|}.$$
--   Here $T_F$ is the damped channel, $\operatorname{Bell}(T)$ its paired Bell output, and $S$ is spectral entropy with natural logarithms. Input and environment types are quantified after the threshold is chosen. Supporting results give a fixed-output entropy modulus for entrywise matrix perturbations, the bound $\|A\|_{\rm HS}\le|I|c$ when all entries of $A$ have magnitude at most $c$, and small-loss control of $2\sqrt{x}+2x$.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/EntropyStability.lean#L21-L93

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
import Definitions.Def_Nonadditivity_DampedBellStability
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyContinuity
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_GeneralBell
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
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
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Output-dimension-only entropy stability from matrix-entry estimates -/

noncomputable section

namespace Nonadditivity.EntropyStability

open Entropy AdjointPurity EntropyContinuity Channels DampedBellStability
open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Entrywise bounds imply an HS bound with only the matrix dimension as
a factor; the index can be unrelated to a channel's input or environment. -/
theorem hsLength_le_card_mul_of_entry_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c) (hA : ∀ i j, ‖A i j‖ ≤ c) :
    hsLength A ≤ (Fintype.card ι : ℝ) * c := by
  have hsq : hsLength A ^ 2 ≤ ((Fintype.card ι : ℝ) * c) ^ 2 := by
    calc
      hsLength A ^ 2 = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
        rw [hsLength_sq]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def]
        simp_rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq]
      _ ≤ ∑ _j : ι, ∑ _i : ι, c ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = ((Fintype.card ι : ℝ) * c) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  exact (sq_le_sq₀ (hsLength_nonneg A) (mul_nonneg (Nat.cast_nonneg _) hc)).mp hsq

/-- A fixed finite output type admits an entropy modulus for coordinatewise
matrix perturbations, uniform over all density matrices. -/
theorem exists_vonNeumann_entry_modulus {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ σ : DensityMatrix ι,
      (∀ i j, ‖ρ.matrix i j - σ.matrix i j‖ ≤ δ) →
        |ρ.vonNeumann - σ.vonNeumann| ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_vonNeumann_hsLength_modulus (ι := ι) η hη
  have hd : 0 < (Fintype.card ι : ℝ) := by positivity
  refine ⟨δ / (Fintype.card ι : ℝ), div_pos hδ hd, fun ρ σ hclose => hmod ρ σ ?_⟩
  have hs := hsLength_le_card_mul_of_entry_bound (ρ.matrix - σ.matrix)
    (δ / (Fintype.card ι : ℝ)) (le_of_lt (div_pos hδ hd)) hclose
  simpa only [mul_div_cancel₀ _ hd.ne'] using hs

/-- The Bell-filter error expression tends uniformly to zero with its
normalized trace loss. No input dimension occurs in this scalar choice. -/
theorem exists_loss_modulus (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ x : ℝ, 0 ≤ x → x < ε → 2 * Real.sqrt x + 2 * x ≤ δ := by
  let t := δ / 4
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨min (t ^ 2) t, lt_min (sq_pos_of_pos ht) ht, fun x _ hx => ?_⟩
  have hx2 : x ≤ t ^ 2 := (hx.trans_le (min_le_left _ _)).le
  have hxt : x ≤ t := (hx.trans_le (min_le_right _ _)).le
  have hs : Real.sqrt x ≤ t := (Real.sqrt_le_left ht.le).mpr hx2
  dsimp [t] at hs hxt
  linarith

universe u v w

/-- The entropy of the genuine damped paired Bell output is stable under
small normalized filter loss. The loss threshold depends only on the
fixed output type and the requested entropy error; input and environment
types are quantified after the threshold has been chosen. -/
theorem exists_damped_bell_entropy_modulus {ο : Type u} [Fintype ο]
    [DecidableEq ο] [Nonempty ο] (η : ℝ) (hη : 0 < η) :
    ∃ ε > 0, ∀ {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]
      [Nonempty ι] [Fintype κ] (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
      (hF : F.IsHermitian) (hres : (1 - F * F).PosSemidef),
      loss F < ε →
        (pairedBellOutput (DampedChannel.damped T F hF hres)).vonNeumann ≤
          (pairedBellOutput T).vonNeumann + η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_vonNeumann_entry_modulus (ι := ο × ο) η hη
  obtain ⟨ε, hε, hsmall⟩ := exists_loss_modulus δ hδ
  refine ⟨ε, hε, ?_⟩
  intro ι κ _ _ _ _ T F hF hres hclose
  have he := hsmall (loss F) (loss_nonneg F hres) hclose
  have hs := hmod (pairedBellOutput (DampedChannel.damped T F hF hres))
    (pairedBellOutput T) (fun a b => (damped_pair_entry_sub_norm_le T F hF hres a b).trans he)
  linarith [(abs_le.mp hs).2]

end Nonadditivity.EntropyStability


