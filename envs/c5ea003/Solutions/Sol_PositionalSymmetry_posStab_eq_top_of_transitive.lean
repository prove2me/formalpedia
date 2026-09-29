-- Prove2me | solution 1 for PositionalSymmetry.posStab_eq_top_of_transitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:04:17.769893+00:00
-- url     : https://prove2.me/submissions/9f6b4ab8-65b2-4590-9c63-e0c2cde9dfba

-- Sol generated from MachineLearning/TransformerUniversality/PositionalSymmetry.lean
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


















open PositionalSymmetry in
omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem solution(p : ι → κ → ℝ) (σ : Equiv.Perm ι)
    (hσ : σ ∈ posStab p) (htrans : ∀ i j, ∃ n : ℕ, (σ ^ n) i = j) :
    posStab p = ⊤ := by
  have hpow : ∀ (n : ℕ) (i : ι), p ((σ ^ n) i) = p i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      have hstep : (σ ^ (n + 1)) i = σ ((σ ^ n) i) := by
        rw [pow_succ']
        rfl
      rw [hstep, hσ ((σ ^ n) i), ih i]
  have hconst : ∀ i j, p i = p j := by
    intro i j
    obtain ⟨n, hn⟩ := htrans i j
    rw [← hn, hpow n i]
  ext τ
  simp only [Subgroup.mem_top, iff_true]
  intro i
  exact (hconst (τ i) i)
