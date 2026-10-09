-- Prove2me | Definitions.Def_Nonadditivity_BellOutput
-- name    : Nonadditivity_BellOutput
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:42.406126+00:00
-- url     : https://prove2.me/theorems/01c39df1-ff7e-4ca3-8771-7116553dc612
-- title:
--   Bell-input entropy bounds for paired finite unitary channels
-- statement:
--   The normalized Bell vector defines a pure state on two copies of a finite system. Paired unitary actions leave it fixed on coincident labels, so the output mixture can combine all coincident labels into one state. For a nonempty family of $K$ unitaries, the entropy of the paired channel's Bell output is at most $2\log K-(\log K)/K$. Equality of output and complementary-output entropies for pure inputs transfers the same upper bound to the tensor product of the complementary channel with its conjugate.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/BellOutput.lean#L27-L312

import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-!
# Concrete normalized Bell states and conjugate-unitary invariance

The Bell vectors and density matrices below are actual finite complex
vectors and positive trace-one matrices. No Bell entropy estimate is
postulated.
-/

noncomputable section

namespace Nonadditivity.BellOutput

open Nonadditivity.Entropy
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The normalized maximally entangled vector. -/
def normalizedBellVector : ι × ι → ℂ :=
  (Real.sqrt (1 / (Fintype.card ι : ℝ)) : ℂ) • bellVector

theorem normalizedBellVector_normSq_sum :
    ∑ z : ι × ι, Complex.normSq (normalizedBellVector z) = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [normalizedBellVector, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity :
      0 ≤ 1 / (Fintype.card ι : ℝ)), Fintype.sum_prod_type, bellVector]
  simp [hd]

/-- The Bell density matrix as a normalized rank-one Gram matrix. -/
def bellState : DensityMatrix (ι × ι) where
  matrix := Matrix.vecMulVec normalizedBellVector (star normalizedBellVector)
  positive := by
    let V : Matrix (ι × ι) Unit ℂ := fun z _ => normalizedBellVector z
    have h := Matrix.posSemidef_self_mul_conjTranspose V
    convert h using 1
    ext z w
    simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec]
  normalized := by
    rw [Matrix.trace_vecMulVec]
    have h := congrArg Complex.ofReal
      (normalizedBellVector_normSq_sum (ι := ι))
    simpa [dotProduct, map_sum, Complex.mul_conj] using h

theorem bellState_matrix :
    (bellState (ι := ι)).matrix =
      Matrix.vecMulVec normalizedBellVector (star normalizedBellVector) := rfl

omit [Nonempty ι] in
/-- The normalized Bell vector is fixed by `U tensor conjugate(U)`. -/
theorem conjugate_unitary_fixes_normalizedBellVector
    (U : unitary (Matrix ι ι ℂ)) :
    ((U : Matrix ι ι ℂ) ⊗ₖ (U : Matrix ι ι ℂ).map (starRingEnd ℂ)) *ᵥ
      normalizedBellVector = normalizedBellVector := by
  exact unitary_kronecker_conjugate_fixes_scaled_bell U _

/-- Entrywise conjugation of an actual unitary is an actual unitary. -/
def conjugateUnitary (U : unitary (Matrix ι ι ℂ)) : unitary (Matrix ι ι ℂ) :=
  ⟨(U : Matrix ι ι ℂ).map (starRingEnd ℂ), by
    rw [Unitary.mem_iff]
    constructor
    · ext i j
      have h := congrArg (fun M : Matrix ι ι ℂ => star (M i j))
        (Unitary.coe_star_mul_self U)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
        Matrix.map_apply, Matrix.one_apply, map_sum, mul_comm] using h
    · ext i j
      have h := congrArg (fun M : Matrix ι ι ℂ => star (M i j))
        (Unitary.coe_mul_star_self U)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
        Matrix.map_apply, Matrix.one_apply, map_sum, mul_comm] using h⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem star_mulVec {κ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) (v : κ → ℂ) :
    star (A *ᵥ v) = star v ᵥ* A.conjTranspose := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
    mul_comm]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Conjugation transports the rank-one matrix of a vector. -/
theorem conjugation_vecMulVec {κ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (v : κ → ℂ) :
    A * Matrix.vecMulVec v (star v) * A.conjTranspose =
      Matrix.vecMulVec (A *ᵥ v) (star (A *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, star_mulVec]

/-- The Bell density matrix is fixed by the conjugate unitary action. -/
theorem conjugate_unitary_fixes_bellState (U : unitary (Matrix ι ι ℂ)) :
    (bellState (ι := ι)).unitaryConjugate (tensorUnitary U (conjugateUnitary U)) =
      bellState := by
  apply DensityMatrix.ext
  change _ * Matrix.vecMulVec normalizedBellVector (star normalizedBellVector) * _ = _
  rw [Matrix.star_eq_conjTranspose, conjugation_vecMulVec]
  have h := conjugate_unitary_fixes_normalizedBellVector U
  simp only [tensorUnitary, conjugateUnitary, h, bellState_matrix]

end Nonadditivity.BellOutput

namespace Nonadditivity.BellOutput

open Nonadditivity.Entropy Nonadditivity.Channels
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

abbrev OffDiagonal (κ : Type*) := {z : κ × κ // z.1 ≠ z.2}
abbrev MergedLabel (κ : Type*) := Option (OffDiagonal κ)

def diagonalEquiv (κ : Type*) : {z : κ × κ // z.1 = z.2} ≃ κ where
  toFun := fun z => z.val.1
  invFun := fun i => ⟨(i,i), rfl⟩
  left_inv := by
    rintro ⟨⟨i,j⟩, h⟩
    cases h
    rfl
  right_inv := fun _ => rfl

omit [Nonempty κ] in
theorem offDiagonal_card :
    Fintype.card (OffDiagonal κ) = Fintype.card κ * (Fintype.card κ - 1) := by
  have hd : Fintype.card {z : κ × κ // z.1 = z.2} = Fintype.card κ :=
    Fintype.card_congr (diagonalEquiv κ)
  change Fintype.card {z : κ × κ // ¬z.1 = z.2} = _
  rw [Fintype.card_subtype_compl, Fintype.card_prod, hd, Nat.mul_sub_left_distrib,
    Nat.mul_one]

def mergedWeights : MergedLabel κ → ℝ
  | none => 1 / (Fintype.card κ : ℝ)
  | some _ => 1 / (Fintype.card κ : ℝ) ^ 2

omit [DecidableEq κ] [Nonempty κ] in
theorem mergedWeights_nonneg (z : MergedLabel κ) : 0 ≤ mergedWeights z := by
  cases z <;> simp [mergedWeights]

theorem mergedWeights_sum : ∑ z : MergedLabel κ, mergedWeights z = 1 := by
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hK : 1 ≤ Fintype.card κ := Fintype.card_pos
  have hm : ((Fintype.card κ - 1 : ℕ) : ℝ) = (Fintype.card κ : ℝ) - 1 := by
    rw [Nat.cast_sub hK]
    simp
  simp only [Fintype.sum_option, mergedWeights, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [offDiagonal_card]
  push_cast
  rw [hm]
  field_simp
  ring

theorem mergedWeights_shannon :
    shannon (mergedWeights (κ := κ)) =
      2 * Real.log (Fintype.card κ) - Real.log (Fintype.card κ) / Fintype.card κ := by
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hK : 1 ≤ Fintype.card κ := Fintype.card_pos
  have hm : ((Fintype.card κ - 1 : ℕ) : ℝ) = (Fintype.card κ : ℝ) - 1 := by
    rw [Nat.cast_sub hK]
    simp
  simp only [shannon, Fintype.sum_option, mergedWeights, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [offDiagonal_card]
  push_cast
  rw [hm]
  simp only [one_div, Real.log_inv, Real.log_pow]
  field_simp
  ring

/-- The pure state associated with a unitary pair acting on a Bell input. -/
def pairState (U : κ → unitary (Matrix ι ι ℂ)) (z : κ × κ) :
    DensityMatrix (ι × ι) :=
  bellState.unitaryConjugate (tensorUnitary (U z.1) (conjugateUnitary (U z.2)))

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem pairState_diagonal (U : κ → unitary (Matrix ι ι ℂ)) (i : κ) :
    pairState U (i,i) = bellState := conjugate_unitary_fixes_bellState (U i)

def mergedStates (U : κ → unitary (Matrix ι ι ℂ)) :
    MergedLabel κ → DensityMatrix (ι × ι)
  | none => bellState
  | some z => pairState U z

def pairedChannel (U : κ → unitary (Matrix ι ι ℂ)) :
    KrausChannel (ι × ι) (ι × ι) (κ × κ) :=
  (KrausChannel.uniformUnitary U).tensor (KrausChannel.uniformUnitary U).conjugate

omit [Nonempty ι] [DecidableEq κ] in
theorem pairedChannel_kraus (U : κ → unitary (Matrix ι ι ℂ)) (z : κ × κ) :
    (pairedChannel U).kraus z = (1 / (Fintype.card κ : ℂ)) •
      (tensorUnitary (U z.1) (conjugateUnitary (U z.2)) : Matrix (ι × ι) (ι × ι) ℂ) := by
  have hs : (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) *
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) = 1 / (Fintype.card κ : ℂ) := by
    rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity : 0 ≤ 1 / (Fintype.card κ : ℝ))]
    simp
  ext ⟨a,b⟩ ⟨c,d⟩
  change ((Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) *
      (U z.1 : Matrix ι ι ℂ) a c) *
      star ((Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) *
        (U z.2 : Matrix ι ι ℂ) b d) =
    (1 / (Fintype.card κ : ℂ)) *
      ((U z.1 : Matrix ι ι ℂ) a c * star ((U z.2 : Matrix ι ι ℂ) b d))
  rw [star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) *
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ)) *
      ((U z.1 : Matrix ι ι ℂ) a c * conj ((U z.2 : Matrix ι ι ℂ) b d)) := by ring
    _ = _ := by rw [hs]

omit [DecidableEq κ] in
/-- The tensor random-unitary output has the actual pure-pair ensemble. -/
theorem pairedChannel_bell_matrix (U : κ → unitary (Matrix ι ι ℂ)) :
    ((pairedChannel U).output bellState).matrix =
      ∑ z : κ × κ, ((1 / (Fintype.card κ : ℝ) ^ 2 : ℝ) : ℂ) •
        (pairState U z).matrix := by
  simp only [KrausChannel.output_matrix, KrausChannel.map]
  apply Finset.sum_congr rfl
  intro z _
  rw [pairedChannel_kraus]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    pairState, DensityMatrix.unitaryConjugate, Matrix.star_eq_conjTranspose]
  congr 1
  simp [pow_two]

omit [Nonempty κ] in
theorem split_pair_sum {E : Type*} [AddCommMonoid E] (f : κ × κ → E) :
    (∑ z : κ × κ, f z) = (∑ i : κ, f (i,i)) + ∑ z : OffDiagonal κ, f z := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun z : κ × κ => z.1 = z.2) f
  have hd : (∑ z : {z : κ × κ // z.1 = z.2}, f z) = ∑ i : κ, f (i,i) := by
    apply Fintype.sum_equiv (diagonalEquiv κ)
    rintro ⟨⟨i,j⟩, h⟩
    cases h
    rfl
  rw [hd] at h
  exact h.symm

/-- All diagonal branches coincide, so their weights merge into one `1/K`. -/
theorem pairedChannel_bell_eq_merged (U : κ → unitary (Matrix ι ι ℂ)) :
    (pairedChannel U).output bellState =
      DensityMatrix.mixture mergedWeights mergedWeights_nonneg mergedWeights_sum
        (mergedStates U) := by
  apply DensityMatrix.ext
  rw [pairedChannel_bell_matrix, split_pair_sum]
  have hdiag : (∑ _i : κ, ((1 / (Fintype.card κ : ℝ) ^ 2 : ℝ) : ℂ) •
      (bellState (ι := ι)).matrix) =
      ((1 / (Fintype.card κ : ℝ) : ℝ) : ℂ) • bellState.matrix := by
    have hk : (Fintype.card κ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_natCast]
    field_simp
  simp only [pairState_diagonal, hdiag,
    DensityMatrix.mixture_matrix, Fintype.sum_option, mergedWeights, mergedStates]

theorem bellState_eq_pureState :
    (bellState (ι := ι)) =
      pureState normalizedBellVector normalizedBellVector_normSq_sum := by
  apply DensityMatrix.ext
  rfl

theorem bellState_entropy_zero : (bellState (ι := ι)).vonNeumann = 0 := by
  rw [bellState_eq_pureState]
  exact pureState_entropy_zero _ _

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem pairState_entropy_zero (U : κ → unitary (Matrix ι ι ℂ)) (z : κ × κ) :
    (pairState U z).vonNeumann = 0 := by
  rw [pairState, DensityMatrix.unitaryConjugate_entropy, bellState_entropy_zero]

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem mergedStates_entropy_zero (U : κ → unitary (Matrix ι ι ℂ))
    (z : MergedLabel κ) : (mergedStates U z).vonNeumann = 0 := by
  cases z
  · exact bellState_entropy_zero
  · exact pairState_entropy_zero U _

/-- The actual mixed-unitary Bell output obeys the manuscript's entropy bound. -/
theorem pairedChannel_bell_entropy_le (U : κ → unitary (Matrix ι ι ℂ)) :
    ((pairedChannel U).output bellState).vonNeumann ≤
      2 * Real.log (Fintype.card κ) - Real.log (Fintype.card κ) / Fintype.card κ := by
  rw [pairedChannel_bell_eq_merged]
  have h := EntropyMixtures.densityMatrix_mixture_entropy_upper mergedWeights
    mergedWeights_nonneg mergedWeights_sum (mergedStates U)
  simp_rw [mergedStates_entropy_zero] at h
  simpa [mergedWeights_shannon] using h

/-- The local complementary-channel Bell estimate for arbitrary finite unitaries.
This proves the quantum claim, rather than assuming a Bell-output entropy bound. -/
theorem complementary_bell_entropy_le (U : κ → unitary (Matrix ι ι ℂ)) :
    (((KrausChannel.uniformUnitary U).complementary.tensor
      (KrausChannel.uniformUnitary U).complementary.conjugate).output bellState).vonNeumann ≤
      2 * Real.log (Fintype.card κ) - Real.log (Fintype.card κ) / Fintype.card κ := by
  have hstate : (pairedChannel U).complementary.output bellState =
      ((KrausChannel.uniformUnitary U).complementary.tensor
        (KrausChannel.uniformUnitary U).complementary.conjugate).output bellState := by
    apply DensityMatrix.ext
    rfl
  have he := (pairedChannel U).pure_output_complementary_entropy_eq
    normalizedBellVector normalizedBellVector_normSq_sum
  rw [← bellState_eq_pureState, hstate] at he
  rw [← he]
  exact pairedChannel_bell_entropy_le U

end Nonadditivity.BellOutput


