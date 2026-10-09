-- Prove2me | Definitions.Def_Nonadditivity_DampedBellStability
-- name    : Nonadditivity_DampedBellStability
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:38:31.802864+00:00
-- url     : https://prove2.me/theorems/0de82541-26f0-47fc-a232-141b3570fa21
-- title:
--   Bell outputs and dimension independent damping stability
-- statement:
--   This bundle defines vectorization, the filtered Bell vector, and the Bell output of a channel paired with its conjugate. For a Hermitian filter $F$ with $I-F^2$ positive semidefinite, its loss is $\delta=\operatorname{Tr}(I-F^2)/d_{\mathrm{in}}$. Every matrix entry of the paired Bell output changes by at most $2\sqrt\delta+2\delta$ under the damped-channel construction. The supporting vector-energy and retained-mass estimates make this bound independent of input and environment dimensions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DampedBellStability.lean#L24-L357

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_GeneralBell
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Bell-output stability under a filter with small normalized trace loss -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.DampedBellStability

open Entropy Channels BellOutput
open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def vectorLength (v : ι → ℂ) : ℝ := ‖WithLp.toLp 2 v‖

omit [DecidableEq ι] in
lemma vectorLength_sq (v : ι → ℂ) :
    vectorLength v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v)

lemma pure_trace (v : ι → ℂ) :
    (Matrix.vecMulVec v (star v)).trace.re = vectorLength v ^ 2 := by
  rw [vectorLength_sq, Matrix.trace_vecMulVec]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [DecidableEq ο] in
lemma pure_map_energy (T : KrausChannel ι ο κ) (v : ι → ℂ) :
    ∑ a, ∑ k, ‖(T.kraus k *ᵥ v) a‖ ^ 2 = vectorLength v ^ 2 := by
  have h := congrArg Complex.re (T.trace_map (Matrix.vecMulVec v (star v)))
  rw [pure_trace] at h
  simp only [KrausChannel.map, conjugation_vecMulVec, Matrix.trace_sum,
    Matrix.trace_vecMulVec, Complex.re_sum, dotProduct, Pi.star_apply,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] at h
  rw [Finset.sum_comm]
  exact h

lemma pure_map_row_energy (T : KrausChannel ι ο κ) (v : ι → ℂ) (a : ο) :
    ∑ k, ‖(T.kraus k *ᵥ v) a‖ ^ 2 ≤ vectorLength v ^ 2 := by
  rw [← pure_map_energy T v]
  exact Finset.single_le_sum (f := fun b => ∑ k, ‖(T.kraus k *ᵥ v) b‖ ^ 2)
    (fun b _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    (Finset.mem_univ a)

lemma map_rank_one_entry (T : KrausChannel ι ο κ) (v w : ι → ℂ) (a b : ο) :
    T.map (Matrix.vecMulVec v (star w)) a b =
      ∑ k, (T.kraus k *ᵥ v) a * star ((T.kraus k *ᵥ w) b) := by
  simp only [KrausChannel.map, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply, Finset.sum_mul, star_sum, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Channel completeness controls each rank-one off-diagonal output entry. -/
theorem map_rank_one_entry_norm_le (T : KrausChannel ι ο κ)
    (v w : ι → ℂ) (a b : ο) :
    ‖T.map (Matrix.vecMulVec v (star w)) a b‖ ≤ vectorLength v * vectorLength w := by
  rw [map_rank_one_entry]
  have htri : ‖∑ k, (T.kraus k *ᵥ v) a * star ((T.kraus k *ᵥ w) b)‖ ≤
      ∑ k, ‖(T.kraus k *ᵥ v) a‖ * ‖(T.kraus k *ᵥ w) b‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le (Finset.univ) (fun k => (T.kraus k *ᵥ v) a * star ((T.kraus k *ᵥ w) b))
  apply htri.trans
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖(T.kraus k *ᵥ v) a‖) (fun k => ‖(T.kraus k *ᵥ w) b‖)
  have hv := pure_map_row_energy T v a
  have hw := pure_map_row_energy T w b
  have hmul := mul_le_mul hv hw
    (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (sq_nonneg _)
  have hn : 0 ≤ ∑ k, ‖(T.kraus k *ᵥ v) a‖ * ‖(T.kraus k *ᵥ w) b‖ :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hvn : 0 ≤ vectorLength v := norm_nonneg _
  have hwn : 0 ≤ vectorLength w := norm_nonneg _
  apply (sq_le_sq₀ hn (mul_nonneg hvn hwn)).mp
  simpa only [mul_pow] using hcs.trans hmul

omit [Fintype ι] [DecidableEq ι] in
lemma rank_one_sub (v w : ι → ℂ) :
    Matrix.vecMulVec v (star v) - Matrix.vecMulVec w (star w) =
      Matrix.vecMulVec (v-w) (star v) + Matrix.vecMulVec w (star (v-w)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.sub_apply, Pi.star_apply, star_sub]
  ring

/-- Pure-input output stability, with no factor depending on the input dimension. -/
theorem pure_map_entry_sub_norm_le (T : KrausChannel ι ο κ)
    (v w : ι → ℂ) (a b : ο) :
    ‖T.map (Matrix.vecMulVec v (star v)) a b -
      T.map (Matrix.vecMulVec w (star w)) a b‖ ≤
      (vectorLength v + vectorLength w) * vectorLength (v-w) := by
  have hsub : T.map (Matrix.vecMulVec v (star v)) - T.map (Matrix.vecMulVec w (star w)) =
      T.map (Matrix.vecMulVec (v-w) (star v)) +
        T.map (Matrix.vecMulVec w (star (v-w))) := by
    change T.linearMap _ - T.linearMap _ = T.linearMap _ + T.linearMap _
    rw [← T.linearMap.map_sub, rank_one_sub, T.linearMap.map_add]
  have he := congrArg (fun M : Matrix ο ο ℂ => M a b) hsub
  simp only [Matrix.sub_apply, Matrix.add_apply] at he
  rw [he]
  have hv := map_rank_one_entry_norm_le T (v-w) v a b
  have hw := map_rank_one_entry_norm_le T w (v-w) a b
  exact (norm_add_le _ _).trans (by nlinarith)

lemma posSemidef_entry_norm_le_trace (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (a b : ι) : ‖A a b‖ ≤ A.trace.re := by
  let R := CFC.sqrt A
  have hR : R.conjTranspose = R :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hRR : R * R.conjTranspose = A := by
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have ht : ∑ i, ∑ j, ‖R i j‖ ^ 2 = A.trace.re := by
    rw [← hRR]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def,
      Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have ha : ∑ j, ‖R a j‖ ^ 2 ≤ A.trace.re := by
    rw [← ht]
    exact Finset.single_le_sum (f := fun i => ∑ j, ‖R i j‖ ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  have hb : ∑ j, ‖R b j‖ ^ 2 ≤ A.trace.re := by
    rw [← ht]
    exact Finset.single_le_sum (f := fun i => ∑ j, ‖R i j‖ ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ b)
  have hsum : 2 * (∑ j, ‖R a j‖ * ‖R b j‖) ≤
      (∑ j, ‖R a j‖ ^ 2) + ∑ j, ‖R b j‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by nlinarith [sq_nonneg (‖R a j‖-‖R b j‖)])
  calc
    ‖A a b‖ = ‖∑ j, R a j * star (R b j)‖ := by
      rw [← hRR]; rfl
    _ ≤ ∑ j, ‖R a j‖ * ‖R b j‖ := by
      simpa only [norm_mul,norm_star] using
        norm_sum_le Finset.univ (fun j => R a j * star (R b j))
    _ ≤ A.trace.re := by linarith

section BellFilter
variable [Nonempty ι]

def vectorize (A : Matrix ι ι ℂ) : ι × ι → ℂ :=
  fun z => (Real.sqrt (1/(Fintype.card ι:ℝ)):ℂ) * A z.1 z.2

lemma vectorize_sq (A : Matrix ι ι ℂ) :
    vectorLength (vectorize A) ^ 2 =
      (A.conjTranspose * A).trace.re / Fintype.card ι := by
  rw [vectorLength_sq]
  simp only [vectorize, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 1/(Fintype.card ι:ℝ)),
    Fintype.sum_prod_type, ← Finset.mul_sum,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  simp_rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]
  ring

lemma vectorize_sub (A B : Matrix ι ι ℂ) : vectorize (A-B) = vectorize A-vectorize B := by
  ext z
  simp [vectorize, mul_sub]

lemma vectorize_one : vectorize (1 : Matrix ι ι ℂ) = normalizedBellVector := by
  ext ⟨i,j⟩
  by_cases h : i=j <;> simp [vectorize,normalizedBellVector,bellVector,Matrix.one_apply,h]

lemma bell_length : vectorLength (normalizedBellVector (ι := ι)) = 1 := by
  have h := normalizedBellVector_normSq_sum (ι := ι)
  simp only [Complex.normSq_eq_norm_sq] at h
  rw [← vectorLength_sq] at h
  have hn : 0 ≤ vectorLength (normalizedBellVector (ι := ι)) := norm_nonneg _
  nlinarith

def filteredBell (F : Matrix ι ι ℂ) : ι × ι → ℂ :=
  (F ⊗ₖ F.map star) *ᵥ normalizedBellVector

lemma filteredBell_eq (F : Matrix ι ι ℂ) (hF : F.IsHermitian) :
    filteredBell F = vectorize (F*F) := by
  ext ⟨i,j⟩
  rw [filteredBell, GeneralBell.tensor_mul_bell]
  dsimp [vectorize]
  congr 1
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  have he := congrArg (fun M : Matrix ι ι ℂ => M k j) hF.eq
  change star (F j k) = F k j at he
  change F i k * star (F j k) = F i k * F k j
  rw [he]

def loss (F : Matrix ι ι ℂ) : ℝ := (1-F*F).trace.re / Fintype.card ι

lemma loss_nonneg (F : Matrix ι ι ℂ) (hres : (1-F*F).PosSemidef) : 0 ≤ loss F := by
  exact div_nonneg (RCLike.nonneg_iff.mp hres.trace_nonneg).1 (Nat.cast_nonneg _)

lemma residual_square_trace_le (F : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) :
    ((1-F*F)*(1-F*F)).trace.re ≤ (1-F*F).trace.re := by
  have hFF : (F*F).PosSemidef := by
    simpa only [hF.eq] using Matrix.posSemidef_conjTranspose_mul_self F
  have hp : 0 ≤ ((1-F*F)*(F*F)).trace.re :=
    (RCLike.nonneg_iff.mp (AdjointPurity.trace_mul_nonneg hres hFF)).1
  have he : (1-F*F)*(F*F) = (1-F*F) - (1-F*F)*(1-F*F) := by noncomm_ring
  rw [he, Matrix.trace_sub, Complex.sub_re] at hp
  linarith

lemma filteredBell_sub_length_sq_le (F : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) :
    vectorLength (filteredBell F-normalizedBellVector)^2 ≤ loss F := by
  rw [filteredBell_eq F hF, ← vectorize_one, ← vectorize_sub, vectorize_sq]
  have hh : (F*F-1).conjTranspose = F*F-1 := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hF.eq,Matrix.conjTranspose_one]
  rw [hh]
  have he : (F*F-1)*(F*F-1) = (1-F*F)*(1-F*F) := by noncomm_ring
  rw [he]
  exact div_le_div_of_nonneg_right (residual_square_trace_le F hF hres) (Nat.cast_nonneg _)

lemma filteredBell_length_sq_le (F : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) : vectorLength (filteredBell F)^2 ≤ 1 := by
  have hFF : (F*F).PosSemidef := by
    simpa only [hF.eq] using Matrix.posSemidef_conjTranspose_mul_self F
  have hp : 0 ≤ ((1-F*F)*(F*F)).trace.re :=
    (RCLike.nonneg_iff.mp (AdjointPurity.trace_mul_nonneg hres hFF)).1
  have htr : 0 ≤ (1-F*F).trace.re := (RCLike.nonneg_iff.mp hres.trace_nonneg).1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hp
  simp only [Matrix.trace_sub,Matrix.trace_one,Complex.sub_re,Complex.natCast_re] at htr
  rw [filteredBell_eq F hF,vectorize_sq,Matrix.conjTranspose_mul,hF.eq]
  apply (div_le_one (by positivity : (0:ℝ)<Fintype.card ι)).mpr
  linarith

lemma filteredBell_mass_loss_le (F : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (_hres : (1-F*F).PosSemidef) :
    1-vectorLength (filteredBell F)^2 ≤ 2*loss F := by
  have hp : 0 ≤ ((1-F*F).conjTranspose*(1-F*F)).trace.re :=
    (RCLike.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (1-F*F)).trace_nonneg).1
  have hh : (1-F*F).conjTranspose = 1-F*F := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hF.eq,Matrix.conjTranspose_one]
  rw [hh] at hp
  have he : (1-F*F)*(1-F*F) = 1-(F*F+F*F)+(F*F)*(F*F) := by noncomm_ring
  simp only [he,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_one,
    Complex.add_re,Complex.sub_re,Complex.natCast_re] at hp
  rw [filteredBell_eq F hF,vectorize_sq,Matrix.conjTranspose_mul,hF.eq]
  dsimp [loss]
  simp only [Matrix.trace_sub,Matrix.trace_one,Complex.sub_re,Complex.natCast_re]
  have hd : (0:ℝ)<Fintype.card ι := by positivity
  field_simp
  nlinarith

variable [Nonempty ο]

def pairedBellOutput (T : KrausChannel ι ο κ) : DensityMatrix (ο×ο) :=
  (T.tensor T.conjugate).output bellState

def retainedBellOutput (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ) : Matrix (ο×ο) (ο×ο) ℂ :=
  (T.tensor T.conjugate).map (Matrix.vecMulVec (filteredBell F) (star (filteredBell F)))

lemma damped_pair_retained_le (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) :
    retainedBellOutput T F ≤ (pairedBellOutput (DampedChannel.damped T F hF hres)).matrix := by
  let D := DampedChannel.damped T F hF hres
  let f := fun (k l : κ ⊕ (ο×ι)) =>
    (D.tensor D.conjugate).kraus (k,l) * (bellState (ι := ι)).matrix *
      ((D.tensor D.conjugate).kraus (k,l)).conjTranspose
  have hf (k l : κ ⊕ (ο×ι)) : 0 ≤ f k l :=
    ((bellState (ι := ι)).positive.mul_mul_conjTranspose_same _).nonneg
  have hsum : (∑ k : κ, ∑ l : κ, f (Sum.inl k) (Sum.inl l)) ≤
      ∑ k : κ ⊕ (ο×ι), ∑ l : κ ⊕ (ο×ι), f k l := by
    rw [Fintype.sum_sum_type]
    have houter : 0 ≤ ∑ k : ο×ι, ∑ l : κ ⊕ (ο×ι), f (Sum.inr k) l :=
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => hf (Sum.inr k) l))
    apply le_trans _ (le_add_of_nonneg_right houter)
    exact Finset.sum_le_sum (fun k _ => by
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg (fun l _ => hf (Sum.inl k) (Sum.inr l))))
  have hterm (k l : κ) : f (Sum.inl k) (Sum.inl l) =
      (T.tensor T.conjugate).kraus (k,l) *
        Matrix.vecMulVec (filteredBell F) (star (filteredBell F)) *
          ((T.tensor T.conjugate).kraus (k,l)).conjTranspose := by
    have hmap : (T.kraus l * F).map star = (T.kraus l).map star * F.map star := by
      ext i j
      simp [Matrix.mul_apply,Matrix.map_apply]
    have hk : (D.tensor D.conjugate).kraus (Sum.inl k,Sum.inl l) =
        (T.tensor T.conjugate).kraus (k,l) * (F ⊗ₖ F.map star) := by
      change (T.kraus k*F) ⊗ₖ (T.kraus l*F).map star =
        (T.kraus k ⊗ₖ (T.kraus l).map star) * (F ⊗ₖ F.map star)
      rw [hmap,Matrix.mul_kronecker_mul]
    dsimp [f]
    rw [hk,Matrix.conjTranspose_mul,bellState_matrix]
    have hz : (F ⊗ₖ F.map star) * Matrix.vecMulVec normalizedBellVector (star normalizedBellVector) *
        (F ⊗ₖ F.map star).conjTranspose =
        Matrix.vecMulVec (filteredBell F) (star (filteredBell F)) :=
      conjugation_vecMulVec (F ⊗ₖ F.map star) normalizedBellVector
    rw [← hz]
    simp only [Matrix.mul_assoc]
  simp only [retainedBellOutput,KrausChannel.map,Fintype.sum_prod_type]
  simp_rw [← hterm]
  simpa only [pairedBellOutput,KrausChannel.output_matrix,KrausChannel.map,
    Fintype.sum_prod_type] using hsum

lemma damped_pair_remainder_trace (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) :
    ((pairedBellOutput (DampedChannel.damped T F hF hres)).matrix-retainedBellOutput T F).trace.re =
      1-vectorLength (filteredBell F)^2 := by
  rw [Matrix.trace_sub,Complex.sub_re,(pairedBellOutput _).normalized]
  simp only [retainedBellOutput,KrausChannel.trace_map,pure_trace,Complex.one_re]

/-- Each entry of the actual paired Bell output is stable under damping.
The bound has no factor depending on the input or environment dimension. -/
theorem damped_pair_entry_sub_norm_le (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (a b : ο×ο) :
    ‖(pairedBellOutput (DampedChannel.damped T F hF hres)).matrix a b -
      (pairedBellOutput T).matrix a b‖ ≤ 2*Real.sqrt (loss F)+2*loss F := by
  have hr := Matrix.le_iff.mp (damped_pair_retained_le T F hF hres)
  have hre := posSemidef_entry_norm_le_trace _ hr a b
  rw [damped_pair_remainder_trace T F hF hres] at hre
  have hmass := filteredBell_mass_loss_le F hF hres
  have hv : vectorLength (filteredBell F) ≤ 1 := by
    have h := filteredBell_length_sq_le F hF hres
    have hnon : 0 ≤ vectorLength (filteredBell F) := norm_nonneg _
    nlinarith
  have hd : vectorLength (filteredBell F-normalizedBellVector) ≤ Real.sqrt (loss F) := by
    have h := filteredBell_sub_length_sq_le F hF hres
    have hs := Real.sq_sqrt (loss_nonneg F hres)
    have hn : 0 ≤ vectorLength (filteredBell F-normalizedBellVector) := norm_nonneg _
    nlinarith [Real.sqrt_nonneg (loss F)]
  have hp := pure_map_entry_sub_norm_le (T.tensor T.conjugate)
    (filteredBell F) normalizedBellVector a b
  rw [bell_length] at hp
  have hret : ‖retainedBellOutput T F a b-(pairedBellOutput T).matrix a b‖ ≤
      2*Real.sqrt (loss F) := by
    have hn : 0 ≤ vectorLength (filteredBell F-normalizedBellVector) := norm_nonneg _
    exact hp.trans (by nlinarith [Real.sqrt_nonneg (loss F)])
  have he : (pairedBellOutput (DampedChannel.damped T F hF hres)).matrix a b -
      (pairedBellOutput T).matrix a b =
      ((pairedBellOutput (DampedChannel.damped T F hF hres)).matrix-retainedBellOutput T F) a b +
        (retainedBellOutput T F a b-(pairedBellOutput T).matrix a b) := by
    simp only [Matrix.sub_apply]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end BellFilter

end Nonadditivity.DampedBellStability


