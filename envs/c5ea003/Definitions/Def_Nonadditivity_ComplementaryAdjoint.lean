-- Prove2me | Definitions.Def_Nonadditivity_ComplementaryAdjoint
-- name    : Nonadditivity_ComplementaryAdjoint
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:38:43.555631+00:00
-- url     : https://prove2.me/theorems/e8850092-6bdc-4421-b148-642d30557ce9
-- title:
--   Tensor words and complementary-channel adjoint identities
-- statement:
--   For finite unitary families in successive factors, tensor words retain the recursively ordered branch and Hilbert-space indices of the actual block channel. The bundle proves the uniform Kraus and square-root weight identities and identifies the complementary-channel adjoint with its Gram matrix and tensor-word polynomial. Output reindexing is included so the matrix expression and finite-channel representation use the same coordinates.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ComplementaryAdjoint.lean#L27-L220

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
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
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
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
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
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




/-!
# The actual complementary adjoint polynomial

This proves the manuscript's Gram channel and polynomial formula from the
actual Kraus implementation. The indices can be arbitrary finite types,
including the tensor-word index set used for blocks.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity.Entropy
open scoped Matrix BigOperators ComplexConjugate

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [Fintype κ]

/-- Complementary adjoints are Gram-polynomial evaluations in the Kraus
operators. This is a matrix identity, including rectangular Kraus families. -/
theorem complementary_adjointMap_eq_gram (T : KrausChannel ι ο κ)
    (A : Matrix κ κ ℂ) :
    T.complementary.adjointMap A =
      ∑ a, ∑ b, A a b • ((T.kraus a).conjTranspose * T.kraus b) := by
  ext i j
  simp only [adjointMap, complementary, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ o, ∑ b, ∑ a, star (T.kraus a o i) * A a b * T.kraus b o j) =
        ∑ o, ∑ a, ∑ b, A a b * (star (T.kraus a o i) * T.kraus b o j) := by
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, ∑ o, A a b * (star (T.kraus a o i) * T.kraus b o j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

variable [Nonempty κ]

 theorem sqrt_weight_product (p : ℝ) (hp : 0 ≤ p) :
    star (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hp]









open Nonadditivity.Entropy
open scoped Kronecker

omit [Nonempty κ] in
/-- Complementing a concrete tensor block gives the tensor block of the
complementary channels, as actual Kraus-channel data. -/
theorem tensorChain_complementary [DecidableEq ο] [DecidableEq κ]
    (T : ℕ → KrausChannel ι ο κ) (n : ℕ) :
    (tensorChain T n).complementary = tensorChain (fun j => (T j).complementary) n := by
  induction n with
  | zero =>
    apply KrausChannel.ext
    funext k
    ext a b
    simp [tensorChain, emptyTensorChannel, complementary]
  | succ n ih =>
    change ((tensorChain T n).tensor (T n)).complementary =
      (tensorChain (fun j => (T j).complementary) n).tensor (T n).complementary
    have hswap : ((tensorChain T n).tensor (T n)).complementary =
        (tensorChain T n).complementary.tensor (T n).complementary := by
      apply KrausChannel.ext
      rfl
    rw [hswap, ih]

/-- Tensor words in the actual block Hilbert space, retaining the ordered
recursively nested branch indices. -/
def tensorWord [DecidableEq κ] (U : ℕ → κ → unitary (Matrix ι ι ℂ)) :
    (n : ℕ) → TensorChainIndex κ n →
      Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ
  | 0, _ => 1
  | n + 1, a => tensorWord U n a.1 ⊗ₖ (U n a.2 : Matrix ι ι ℂ)

/-- The actual tensor-unitary Kraus operators are exactly the tensor words
times the product of their normalized square-root branch weights. -/
theorem tensorChain_uniform_kraus [DecidableEq κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ) (a : TensorChainIndex κ n) :
    (tensorChain (fun j => uniformUnitary (U j)) n).kraus a =
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n • tensorWord U n a := by
  induction n with
  | zero =>
    ext i j
    cases i
    cases j
    simp [tensorChain, emptyTensorChannel, tensorWord]
    rfl
  | succ n ih =>
    rcases a with ⟨a,b⟩
    change (tensorChain (fun j => uniformUnitary (U j)) n).kraus a ⊗ₖ
      (uniformUnitary (U n)).kraus b = _
    rw [ih]
    simp only [uniformUnitary, randomUnitary, tensorWord, Matrix.smul_kronecker,
      Matrix.kronecker_smul, smul_smul, pow_succ]
    rw [mul_comm]
    rfl

/-- The precise normalized polynomial for the actual complementary tensor
block, before standardizing its output labels. -/
theorem blockComplementary_adjoint_eq_tensor_polynomial [DecidableEq κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ)
    (A : Matrix (TensorChainIndex κ n) (TensorChainIndex κ n) ℂ) :
    (Nonadditivity.BlockBell.blockComplementary U n).adjointMap A =
      (1 / (Fintype.card κ : ℂ)) ^ n •
        ∑ a, ∑ b, A a b •
          ((tensorWord U n a).conjTranspose * tensorWord U n b) := by
  change (tensorChain (fun j => (uniformUnitary (U j)).complementary) n).adjointMap A = _
  rw [← tensorChain_complementary, complementary_adjointMap_eq_gram]
  simp_rw [tensorChain_uniform_kraus]
  have hweight :
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n *
        star ((Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n) =
      (1 / (Fintype.card κ : ℂ)) ^ n := by
    rw [star_pow, ← mul_pow, mul_comm]
    rw [Nonadditivity.Channels.KrausChannel.sqrt_weight_product _ (by positivity : 0 ≤ 1 / (Fintype.card κ : ℝ))]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hweight, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (A a b)]

omit [Nonempty κ] in
/-- Changing only the output labels pulls the observable back by that
same equivalence. This is proved from the Kraus adjoint formula. -/
theorem reindex_output_adjointMap {ν : Type*} [Fintype ν]
    (T : KrausChannel ι ο κ) (e : ο ≃ ν) (A : Matrix ν ν ℂ) :
    (T.reindex (Equiv.refl ι) e).adjointMap A =
      T.adjointMap (A.submatrix e e) := by
  have hA : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp
  conv_lhs => rw [← hA]
  simp only [adjointMap, reindex, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  rfl

/-- The exact normalized tensor-word polynomial of the manuscript, now for
the actual `blockChannel` with its explicitly standardized output basis. -/
theorem blockChannel_adjoint_eq_tensor_polynomial {K : ℕ} [NeZero K]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    (Nonadditivity.BlockConstruction.blockChannel U n).adjointMap A =
      (1 / ((K : ℂ) ^ n)) •
        ∑ a, ∑ b,
          A (Nonadditivity.BlockConstruction.blockOutputEquiv K n a)
            (Nonadditivity.BlockConstruction.blockOutputEquiv K n b) •
          ((tensorWord U n a).conjTranspose * tensorWord U n b) := by
  unfold Nonadditivity.BlockConstruction.blockChannel
  rw [reindex_output_adjointMap, blockComplementary_adjoint_eq_tensor_polynomial]
  simp only [Fintype.card_fin, one_div, inv_pow, Matrix.submatrix_apply]

end Nonadditivity.Channels.KrausChannel


