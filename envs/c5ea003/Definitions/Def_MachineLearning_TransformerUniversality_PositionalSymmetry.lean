-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_PositionalSymmetry
-- name    : MachineLearning_TransformerUniversality_PositionalSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:47.306621+00:00
-- url     : https://prove2.me/theorems/64d6f8bb-ec1b-446c-b542-3767d579332e
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_PositionalSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.PositionalSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/PositionalSymmetry.lean by skeleton subtraction
import Mathlib

/-!
# Permutation symmetry and how additive positional encodings destroy it

`Catalog/MachineLearning/SoftmaxAttentionEquivariance.lean` proves that softmax attention is
permutation equivariant, and `Catalog/MachineLearning/TransformerArchitecture.lean` introduces
additive positional encodings but proves nothing about the interaction of the two.  This file
determines that interaction **exactly**.

Working with the bilinear (pre-softmax) attention score of the catalog architecture, we show:

* `linAttention_equivariant` — with no positional encoding, the whole attention read is
  equivariant under every simultaneous token permutation;
* `posScore_equivariant_iff` — with an additive positional encoding `p`, a permutation `σ`
  preserves all scores for all inputs **iff** `p ∘ σ = p`;
* `posStab` — consequently the residual symmetry group is exactly the stabilizer subgroup of
  the positional encoding, and `mem_posStab_iff` identifies it with the equivariant
  permutations;
* `posStab_eq_bot_of_injective` — pairwise distinct positional encodings destroy *all*
  permutation symmetry;
* `exists_symmetry_breaking` and `two_token_symmetry_breaking` — an explicit two-token
  counterexample.
-/

open scoped BigOperators

namespace PositionalSymmetry

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Feature-space inner product used by the bilinear attention score. -/
def dot (u v : κ → ℝ) : ℝ := ∑ a, u a * v a



/-- Reindex a token-indexed tensor by a permutation. -/
def permute (σ : Equiv.Perm ι) (x : ι → κ → ℝ) : ι → κ → ℝ := fun i => x (σ.symm i)

/-- Bilinear attention score with an additive positional encoding `p`. -/
def posScore (p x : ι → κ → ℝ) (i j : ι) : ℝ :=
  dot (fun a => x i a + p i a) (fun a => x j a + p j a)

/-- Bilinear attention read (linear attention, no softmax). -/
def linAttention (x : ι → κ → ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, dot (x i) (x j) * v j



/-- The stabilizer subgroup of a positional encoding: the residual symmetry group of a
transformer layer with additive positional encodings. -/
def posStab (p : ι → κ → ℝ) : Subgroup (Equiv.Perm ι) where
  carrier := {σ | ∀ i, p (σ i) = p i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro a b ha hb i
    simp only [Equiv.Perm.mul_apply]
    rw [ha (b i), hb i]
  inv_mem' := by
    intro a ha i
    have h := ha (a.symm i)
    rw [Equiv.apply_symm_apply] at h
    simp only [Equiv.Perm.inv_def]
    rw [← h]








end PositionalSymmetry


