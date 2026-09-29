-- Prove2me | Theorems.Thm_PositionalSymmetry_posScore_equivariant_iff
-- name    : PositionalSymmetry.posScore_equivariant_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:51:00.87011+00:00
-- url     : https://prove2.me/theorems/eddd2677-617e-4053-8749-eff58bf9e4ab
-- title:
--   **Positional encodings break permutation symmetry exactly on the non-stabilizing
-- statement:
--   **Positional encodings break permutation symmetry exactly on the non-stabilizing
--   permutations.**  For at least two tokens, `σ` preserves every positionally-encoded score for
--   every input if and only if `σ` fixes the positional encoding pointwise.
--
--   ```lean
--   theorem PositionalSymmetry.posScore_equivariant_iff(hcard : 2 ≤ Fintype.card ι)
--       (σ : Equiv.Perm ι) (p : ι → κ → ℝ) :
--       (∀ x : ι → κ → ℝ, ∀ i j, posScore p (permute σ x) (σ i) (σ j) = posScore p x i j)
--         ↔ ∀ i, p (σ i) = p i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/PositionalSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/PositionalSymmetry.lean#L63

-- Thm stub generated from MachineLearning/TransformerUniversality/PositionalSymmetry.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PositionalSymmetry

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

open PositionalSymmetry

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem PositionalSymmetry.posScore_equivariant_iff(hcard : 2 ≤ Fintype.card ι)
    (σ : Equiv.Perm ι) (p : ι → κ → ℝ) :
    (∀ x : ι → κ → ℝ, ∀ i j, posScore p (permute σ x) (σ i) (σ j) = posScore p x i j)
      ↔ ∀ i, p (σ i) = p i := by sorry
