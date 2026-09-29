-- Prove2me | solution 1 for PositionalSymmetry.no_cyclic_residual_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:08:35.661689+00:00
-- url     : https://prove2.me/submissions/1a731079-fc58-4191-a994-ddac243c30b7

-- Sol generated from MachineLearning/TransformerUniversality/PositionalSymmetry.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PositionalSymmetry
import Theorems.Thm_PositionalSymmetry_posStab_eq_top_of_transitive

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













omit [Fintype κ] in
/-- Concretely, on three positions a three-cycle symmetry forces total permutation
invariance. -/
theorem three_cycle_symmetry_forces_top (p : Fin 3 → κ → ℝ)
    (h : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ∈ posStab p) :
    posStab p = ⊤ := by
  refine posStab_eq_top_of_transitive p _ h ?_
  intro i j
  refine ⟨(j - i : Fin 3).val, ?_⟩
  fin_cases i <;> fin_cases j <;> decide





open PositionalSymmetry in
omit [Fintype κ] in
theorem solution:
    ¬ ∃ p : Fin 3 → κ → ℝ,
      posStab p = Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) := by
  rintro ⟨p, hp⟩
  have hc : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ∈ posStab p := by
    rw [hp]; exact Subgroup.mem_zpowers _
  have htop := three_cycle_symmetry_forces_top p hc
  have hmem : Equiv.swap (0 : Fin 3) 1 ∈
      Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) := by
    rw [← hp, htop]; trivial
  obtain ⟨k, hk⟩ := hmem
  have hsign := congrArg Equiv.Perm.sign hk
  rw [map_zpow] at hsign
  have hc1 : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 1 := by decide
  have hc2 : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
  rw [hc1, hc2, one_zpow] at hsign
  exact absurd hsign (by decide)
