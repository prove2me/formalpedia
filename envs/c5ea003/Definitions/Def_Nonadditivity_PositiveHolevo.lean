-- Prove2me | Definitions.Def_Nonadditivity_PositiveHolevo
-- name    : Nonadditivity_PositiveHolevo
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:42:58.086549+00:00
-- url     : https://prove2.me/theorems/7b6e70f1-4bb2-42e7-9f08-5accb489a858
-- title:
--   Merged branch weights and pure-input spectral witnesses
-- statement:
--   For distinct labels $a,b$ in a nonempty finite branch set of size $K$, the merged weights are $2/K$ at $a$, zero at $b$, and $1/K$ elsewhere. They form a normalized probability vector with reduced Shannon entropy. The bundle supplies normalized eigenvector and pure-input witnesses that make two unitary branch outputs agree, and the corresponding complementary/block output entropy bounds. These witnesses support strict positivity of the converted channel information.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/PositiveHolevo.lean#L25-L258

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
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HolevoBits
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_Scalar
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # A universal lower bound for the constructed channel's Holevo quantity

The witnesses are actual pure inputs, obtained from complex eigenvectors of
the relative unitary of two branches. No adjoint norm bound is used.
-/

noncomputable section

namespace Nonadditivity.PositiveHolevo

open Entropy Channels Channels.KrausChannel BlockConstruction Conversion
open scoped BigOperators ComplexOrder ComplexConjugate Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every complex square matrix on a nonempty finite space has a normalized
eigenvector. Normalization uses the actual sum of coordinate norm squares. -/
theorem exists_normalized_eigenvector (M : Matrix ι ι ℂ) :
    ∃ z : ℂ, ∃ v : ι → ℂ,
      (∑ i, Complex.normSq (v i)) = 1 ∧ M *ᵥ v = z • v := by
  obtain ⟨z,hz⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
  obtain ⟨x,hx⟩ := hz.exists_hasEigenvector
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hx.2
  have hS : 0 < ∑ i, Complex.normSq (x i) := by
    apply Finset.sum_pos'
    · intro i _
      exact Complex.normSq_nonneg _
    · exact ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  let r : ℝ := Real.sqrt (∑ i, Complex.normSq (x i))
  have hr : 0 < r := Real.sqrt_pos.mpr hS
  let v : ι → ℂ := Complex.ofReal (r⁻¹) • x
  refine ⟨z,v,?_,?_⟩
  · simp only [v, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, ← Finset.mul_sum]
    have hs : r * r = ∑ i, Complex.normSq (x i) := Real.mul_self_sqrt hS.le
    rw [← hs]
    field_simp [ne_of_gt hr]
  · have he : M *ᵥ x = z • x := by
      simpa only [Matrix.toLin'_apply] using hx.apply_eq_smul
    dsimp only [v]
    rw [Matrix.mulVec_smul, he, smul_smul, smul_smul, mul_comm]

/-- Two unitary branches have a pure input whose output projections agree.
The phase modulus is derived from trace normalization of the actual states. -/
theorem exists_pure_input_equal_unitary_outputs
    (U V : unitary (Matrix ι ι ℂ)) :
    ∃ v : ι → ℂ, ∃ hv : (∑ i, Complex.normSq (v i)) = 1,
      (pureState v hv).unitaryConjugate U = (pureState v hv).unitaryConjugate V := by
  obtain ⟨z,v,hv,he⟩ := exists_normalized_eigenvector
    ((U : Matrix ι ι ℂ).conjTranspose * (V : Matrix ι ι ℂ))
  have hUV : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ).conjTranspose = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hphase : (V : Matrix ι ι ℂ) *ᵥ v = z • ((U : Matrix ι ι ℂ) *ᵥ v) := by
    have h := congrArg (fun x => (U : Matrix ι ι ℂ) *ᵥ x) he
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hUV,
      Matrix.one_mul, Matrix.mulVec_smul] using h
  let σ := (pureState v hv).unitaryConjugate U
  let τ := (pureState v hv).unitaryConjugate V
  have hm : τ.matrix = (Complex.normSq z : ℂ) • σ.matrix := by
    change (V : Matrix ι ι ℂ) * Matrix.vecMulVec v (star v) * _ =
      (Complex.normSq z : ℂ) •
        ((U : Matrix ι ι ℂ) * Matrix.vecMulVec v (star v) * _)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      BellOutput.conjugation_vecMulVec, BellOutput.conjugation_vecMulVec, hphase]
    ext a b
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_mul,
      smul_eq_mul, Matrix.smul_apply]
    rw [← Complex.mul_conj z]
    simp only [Complex.star_def]
    ring
  have hz : (Complex.normSq z : ℂ) = 1 := by
    have ht := congrArg Matrix.trace hm
    simpa only [τ.normalized, Matrix.trace_smul, σ.normalized, smul_eq_mul, mul_one] using ht.symm
  refine ⟨v,hv,?_⟩
  apply DensityMatrix.ext
  exact (hm.trans (by rw [hz, one_smul])).symm

section MergedWeights

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- The two first branch weights are merged, retaining a zero-weight label. -/
def twoMergedWeights (a b : κ) (i : κ) : ℝ :=
  if i = a then 2 / (Fintype.card κ : ℝ)
  else if i = b then 0 else 1 / (Fintype.card κ : ℝ)

theorem twoMergedWeights_nonneg (a b i : κ) : 0 ≤ twoMergedWeights a b i := by
  unfold twoMergedWeights
  split_ifs <;> positivity

omit [Nonempty κ] in
theorem twoMergedWeights_eq (a b : κ) (hab : a ≠ b) (i : κ) :
    twoMergedWeights a b i = 1 / (Fintype.card κ : ℝ) +
      (if i = a then 1 / (Fintype.card κ : ℝ) else 0) -
      (if i = b then 1 / (Fintype.card κ : ℝ) else 0) := by
  by_cases ha : i = a
  · subst i
    simp [twoMergedWeights, hab]
    ring
  · by_cases hb : i = b
    · subst i
      simp [twoMergedWeights, Ne.symm hab]
    · simp [twoMergedWeights, ha, hb]

theorem twoMergedWeights_sum (a b : κ) (hab : a ≠ b) :
    ∑ i, twoMergedWeights a b i = 1 := by
  simp_rw [twoMergedWeights_eq a b hab]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [Fintype.card_ne_zero]

theorem twoMergedWeights_shannon (a b : κ) (hab : a ≠ b) :
    shannon (twoMergedWeights a b) = Real.log (Fintype.card κ) -
      2 * Real.log 2 / (Fintype.card κ : ℝ) := by
  have hK : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hterm (i : κ) :
      twoMergedWeights a b i * Real.log (twoMergedWeights a b i) =
        (1 / (Fintype.card κ : ℝ)) * Real.log (1 / (Fintype.card κ : ℝ)) +
        (if i = a then
          (2 / (Fintype.card κ : ℝ)) * Real.log (2 / (Fintype.card κ : ℝ)) -
            (1 / (Fintype.card κ : ℝ)) * Real.log (1 / (Fintype.card κ : ℝ))
         else 0) -
        (if i = b then
          (1 / (Fintype.card κ : ℝ)) * Real.log (1 / (Fintype.card κ : ℝ))
         else 0) := by
    by_cases ha : i = a
    · subst i
      simp [twoMergedWeights, hab]
    · by_cases hb : i = b
      · subst i
        simp [twoMergedWeights, Ne.symm hab]
      · simp [twoMergedWeights, ha, hb]
  unfold shannon
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hK]
  simp only [one_div, Real.log_inv]
  field_simp
  ring

omit [Nonempty ι] in
set_option maxHeartbeats 150000 in
/-- The equality of two actual output states merges their weights in the
actual random-unitary output matrix. No orthogonality is needed. -/
theorem uniformUnitary_output_eq_twoMerged
    (U : κ → unitary (Matrix ι ι ℂ)) (ρ : DensityMatrix ι)
    (a b : κ) (hab : a ≠ b)
    (heq : ρ.unitaryConjugate (U a) = ρ.unitaryConjugate (U b)) :
    (uniformUnitary U).output ρ =
      DensityMatrix.mixture (twoMergedWeights a b) (twoMergedWeights_nonneg a b)
        (twoMergedWeights_sum a b hab) (fun i => ρ.unitaryConjugate (U i)) := by
  let pu : κ → ℝ := fun _ => 1 / (Fintype.card κ : ℝ)
  have hpu : ∀ i, 0 ≤ pu i := fun _ => by dsimp [pu]; positivity
  have hsu : ∑ i, pu i = 1 := by simp [pu, Fintype.card_ne_zero]
  have houtput : (uniformUnitary U).output ρ =
      DensityMatrix.mixture pu hpu hsu (fun i => ρ.unitaryConjugate (U i)) := by
    apply DensityMatrix.ext
    change (randomUnitary _ _ _ U).map ρ.matrix = _
    rw [randomUnitary_map]
    simp only [DensityMatrix.mixture_matrix, DensityMatrix.unitaryConjugate,
      Matrix.star_eq_conjTranspose, pu]
  rw [houtput]
  apply DensityMatrix.ext
  simp only [DensityMatrix.mixture_matrix]
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hp (i : κ) : (twoMergedWeights a b i : ℂ) =
      Complex.ofReal (1 / (Fintype.card κ : ℝ)) +
      (if i = a then Complex.ofReal (1 / (Fintype.card κ : ℝ)) else 0) -
      (if i = b then Complex.ofReal (1 / (Fintype.card κ : ℝ)) else 0) := by
    have hh := congrArg Complex.ofReal (twoMergedWeights_eq a b hab i)
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, apply_ite,
      Complex.ofReal_zero] using hh
  have hterm (i : κ) : (twoMergedWeights a b i : ℂ) *
      (ρ.unitaryConjugate (U i)).matrix x y =
      Complex.ofReal (1 / (Fintype.card κ : ℝ)) * (ρ.unitaryConjugate (U i)).matrix x y +
      (if i = a then Complex.ofReal (1 / (Fintype.card κ : ℝ)) *
        (ρ.unitaryConjugate (U i)).matrix x y else 0) -
      (if i = b then Complex.ofReal (1 / (Fintype.card κ : ℝ)) *
        (ρ.unitaryConjugate (U i)).matrix x y else 0) := by
    rw [hp]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [heq]
  simp only [pu, add_sub_cancel_right]

/-- The phase-aligned eigenvector is an actual local complementary-channel
input with the stated output entropy deficit. -/
theorem exists_complementary_entropy_le
    (U : κ → unitary (Matrix ι ι ℂ)) (a b : κ) (hab : a ≠ b) :
    ∃ ρ : DensityMatrix ι,
      ((uniformUnitary U).complementary.output ρ).vonNeumann ≤
        Real.log (Fintype.card κ) - 2 * Real.log 2 / (Fintype.card κ : ℝ) := by
  obtain ⟨v,hv,heq⟩ := exists_pure_input_equal_unitary_outputs (U a) (U b)
  let ρ := pureState v hv
  have hm := uniformUnitary_output_eq_twoMerged U ρ a b hab heq
  have h := EntropyMixtures.densityMatrix_mixture_entropy_upper
    (twoMergedWeights a b) (twoMergedWeights_nonneg a b)
    (twoMergedWeights_sum a b hab) (fun i => ρ.unitaryConjugate (U i))
  have hz (i : κ) : (ρ.unitaryConjugate (U i)).vonNeumann = 0 := by
    rw [DensityMatrix.unitaryConjugate_entropy]
    exact pureState_entropy_zero v hv
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero,
    twoMergedWeights_shannon a b hab] at h
  refine ⟨ρ,?_⟩
  rw [← (uniformUnitary U).pure_output_complementary_entropy_eq v hv, hm]
  exact h

end MergedWeights

/-- Product inputs tensor the actual local eigenvector witnesses. -/
theorem exists_block_entropy_le {K : ℕ} [NeZero K] (hK : 2 ≤ K)
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    ∃ ρ : DensityMatrix (TensorChainIndex ι n),
      ((blockChannel U n).output ρ).vonNeumann ≤
        (n : ℝ) * (Real.log K - 2 * Real.log 2 / (K : ℝ)) := by
  let a : Fin K := ⟨0, by omega⟩
  let b : Fin K := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg Fin.val h
    change (0 : ℕ) = 1 at h'
    omega
  have hex (j : ℕ) := exists_complementary_entropy_le (U j) a b hab
  choose ρ hρ using hex
  let σ := DensityMatrix.tensorChain ρ n
  have hsum : ((BlockBell.blockComplementary U n).output σ).vonNeumann ≤
      (n : ℝ) * (Real.log K - 2 * Real.log 2 / (K : ℝ)) := by
    change ((tensorChain (fun j => (uniformUnitary (U j)).complementary) n).output
      (DensityMatrix.tensorChain ρ n)).vonNeumann ≤ _
    rw [tensorChain_output_entropy]
    calc
      _ ≤ ∑ j ∈ Finset.range n,
          (Real.log K - 2 * Real.log 2 / (K : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Fintype.card_fin] using hρ j
      _ = _ := by simp; ring
  have hout := reindex_output_eq (BlockBell.blockComplementary U n)
    (Equiv.refl _) (blockOutputEquiv K n) σ
  rw [DensityMatrix.reindex_refl] at hout
  refine ⟨σ,?_⟩
  change (((BlockBell.blockComplementary U n).reindex (Equiv.refl _)
    (blockOutputEquiv K n)).output σ).vonNeumann ≤ _
  rw [hout, DensityMatrix.reindex_entropy]
  exact hsum







end Nonadditivity.PositiveHolevo


