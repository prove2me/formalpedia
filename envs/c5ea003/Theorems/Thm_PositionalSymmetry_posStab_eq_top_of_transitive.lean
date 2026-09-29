-- Prove2me | Theorems.Thm_PositionalSymmetry_posStab_eq_top_of_transitive
-- name    : PositionalSymmetry.posStab_eq_top_of_transitive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:49:41.363971+00:00
-- url     : https://prove2.me/theorems/c8ab9636-1d7b-4daa-ab59-a8713e34cb8b
-- title:
--   A transitive symmetry destroys all positional information.
-- statement:
--   **A transitive symmetry destroys all positional information.**  If a permutation whose
--   powers act transitively on positions is a symmetry of the encoding, then the encoding is
--   constant and *every* permutation is a symmetry.
--
--   ```lean
--   theorem PositionalSymmetry.posStab_eq_top_of_transitive(p : ι → κ → ℝ) (σ : Equiv.Perm ι)
--       (hσ : σ ∈ posStab p) (htrans : ∀ i j, ∃ n : ℕ, (σ ^ n) i = j) :
--       posStab p = ⊤ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/PositionalSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/PositionalSymmetry.lean#L143

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












omit [Fintype ι] [DecidableEq ι] [Fintype κ] in

theorem PositionalSymmetry.posStab_eq_top_of_transitive(p : ι → κ → ℝ) (σ : Equiv.Perm ι)
    (hσ : σ ∈ posStab p) (htrans : ∀ i j, ∃ n : ℕ, (σ ^ n) i = j) :
    posStab p = ⊤ := by sorry
