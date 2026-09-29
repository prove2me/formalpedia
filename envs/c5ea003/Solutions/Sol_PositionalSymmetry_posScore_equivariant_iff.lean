-- Prove2me | solution 1 for PositionalSymmetry.posScore_equivariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:08:36.21998+00:00
-- url     : https://prove2.me/submissions/cd336dff-30f6-40ae-947e-1063e6a919ff

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


theorem dot_add_right (u v w : κ → ℝ) :
    dot u (fun a => v a + w a) = dot u v + dot u w := by
  simp only [dot, mul_add, Finset.sum_add_distrib]

theorem dot_self_eq_zero {u : κ → ℝ} (h : dot u u = 0) : ∀ a, u a = 0 := by
  intro a
  have hnn : ∀ b ∈ (Finset.univ : Finset κ), 0 ≤ u b * u b := fun b _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h a (Finset.mem_univ a)
  exact by nlinarith [this]















open PositionalSymmetry in
theorem solution(hcard : 2 ≤ Fintype.card ι)
    (σ : Equiv.Perm ι) (p : ι → κ → ℝ) :
    (∀ x : ι → κ → ℝ, ∀ i j, posScore p (permute σ x) (σ i) (σ j) = posScore p x i j)
      ↔ ∀ i, p (σ i) = p i := by
  constructor
  · intro hall i
    obtain ⟨j, hj⟩ : ∃ j : ι, j ≠ i := by
      obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
      by_cases h : a = i
      · exact ⟨b, fun hb => hab (by rw [h, hb])⟩
      · exact ⟨a, h⟩
    -- Step 1: the purely positional term is preserved.
    have hzero := hall (fun _ _ => 0) i j
    simp only [posScore, permute, zero_add] at hzero
    -- Step 2: probe with an input supported at `j`.
    have hprobe : ∀ y : κ → ℝ, dot (p (σ i)) y = dot (p i) y := by
      intro y
      set x : ι → κ → ℝ := fun m => if m = j then y else fun _ => 0 with hxdef
      have hxi : x i = fun _ => (0:ℝ) := by
        simp only [hxdef, if_neg (Ne.symm hj)]
      have hxj : x j = y := by simp only [hxdef, if_pos rfl]
      have h := hall x i j
      simp only [posScore, permute, Equiv.symm_apply_apply, hxi, hxj, zero_add] at h
      rw [dot_add_right, dot_add_right] at h
      linarith [h, hzero]
    -- Step 3: a self-probe forces the two positional vectors to agree.
    funext a
    have hdiff : dot (fun b => p (σ i) b - p i b) (fun b => p (σ i) b - p i b) = 0 := by
      have h1 := hprobe (fun b => p (σ i) b - p i b)
      simp only [dot, sub_mul, Finset.sum_sub_distrib] at h1 ⊢
      have h2 : ∑ b, p (σ i) b * (p (σ i) b - p i b)
          = ∑ b, p i b * (p (σ i) b - p i b) := by
        simpa [dot, mul_sub, Finset.sum_sub_distrib] using h1
      simp only [mul_sub, Finset.sum_sub_distrib] at h2
      linarith [h2]
    have := dot_self_eq_zero hdiff a
    linarith [this]
  · intro hp x i j
    simp only [posScore, permute, Equiv.symm_apply_apply, hp]
