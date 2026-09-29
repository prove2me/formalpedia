-- Prove2me | Definitions.Def_mme_complete_split_profile_projection
-- name    : mme_complete_split_profile_projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T16:59:22.864852+00:00
-- url     : https://prove2.me/theorems/0cb31b9f-f1cc-4f26-b9ea-828c260057dc
-- title:
--   All-mode complete-split profile projections
-- statement:
--   Choose a basis in each of the three modes of an arbitrary tensor. Assign every basis vector a full level-1 word of length 2^(ell-1), where ell>=1, and fix three nonnegative normalized real complete-split distributions and a nonnegative error epsilon. In T^N, retain a mode-basis word precisely when, for every full fine word sigma, |count(sigma)-N*beta(sigma)|<=N*epsilon. The resulting tensor is the all-zero block of the basis grading that puts retained vectors in class zero and all other vectors in class one. For N>0 this is the paper's empirical sup-norm consistency test. At N=0, keep the unique empty word by explicit convention. Labels for canonical CW constituents must be separately identified; this definition assumes no asymptotic value or extraction theorem.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v3, printed pp.14-15, Definitions3.4-3.6. This is the finite all-mode projection layer; canonical CW labeling and the asymptotic degeneration/limit theorems remain separate.

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_kron_pow_mode_word_basis
import Mathlib.Data.NNReal.Basic

/-!
Finite all-three-mode complete-split projection from More Asymmetry,
Definitions 3.4--3.6. A mode label records a full fine word, not only a
left-half grade. Canonical labels for a particular CW constituent must be
supplied and justified separately.

The scaled-count predicate agrees with the source empirical-frequency
predicate at positive powers. At power zero we explicitly keep the unique
empty word; this is a convention, not the undefined empirical 0/0 formula.
-/

set_option autoImplicit false
set_option warningAsError true

universe u

namespace MME

open Module BigOperators DWZComponentRestriction
open scoped NNReal

/-- Split all three chosen mode bases into allowed and disallowed vectors. -/
noncomputable def TensorObj.basisAllAllowedGrading
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) : T.TypeGrading 2 := by
  classical
  exact {
    decomp := fun i ↦ cwBasisGrade (b i)
      (fun j ↦ if allowed i j then (0 : Fin 2) else 1)
    is_internal := fun i ↦ cwBasisGrade_isInternal (b i)
      (fun j ↦ if allowed i j then (0 : Fin 2) else 1) }

/-- One simultaneous mode-wise projection of T, not a sum of tensor copies. -/
noncomputable def TensorObj.basisAllAllowedSubtensor
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) : TensorObj K 3 :=
  (T.basisAllAllowedGrading b allowed).blockSubtensor (fun _ ↦ 0)

namespace CompleteSplit

/-- The full level-1 label word of one level-ell factor. -/
abbrev CompleteWord (ell : ℕ) := Fin (2 ^ (ell - 1)) → Fin 3

/-- A complete-split probability distribution at a valid positive level. -/
structure Profile (ell : ℕ) where
  level_pos : 1 ≤ ell
  probability : CompleteWord ell → ℝ
  nonnegative : ∀ sigma, 0 ≤ probability sigma
  sum_eq_one : ∑ sigma, probability sigma = 1

/-- Count one complete fine word among the N constituent-factor positions. -/
def wordCount {ι : Type u} {ell N : ℕ}
    (label : ι → CompleteWord ell) (w : PowIndex ι N)
    (sigma : CompleteWord ell) : ℕ :=
  (Finset.univ.filter
    (fun r : Fin N ↦ label (PowIndex.get N w r) = sigma)).card

/-- Source sup-norm approximate consistency in denominator-free form.
For N>0, divide both sides by N. For N=0 every empty word is allowed. -/
def ApproxConsistent {ι : Type u} {ell N : ℕ}
    (label : ι → CompleteWord ell) (beta : Profile ell)
    (epsilon : ℝ≥0) (w : PowIndex ι N) : Prop :=
  ∀ sigma : CompleteWord ell,
    |(wordCount label w sigma : ℝ) - (N : ℝ) * beta.probability sigma| ≤
      (N : ℝ) * (epsilon : ℝ)

/-- Literal all-mode complete-profile restriction of T^N. Each supplied label
records the entire fine word of a basis vector of one constituent factor.
This definition does not identify arbitrary labels with canonical CW labels. -/
noncomputable def restrictedPower
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) : TensorObj K 3 :=
  (T.kronPow N).basisAllAllowedSubtensor
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (label i) (beta i) epsilon)

end CompleteSplit

end MME


