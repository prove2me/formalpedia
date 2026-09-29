-- Prove2me | solution 1 for sparseAttendCount_le_2B
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:03:53.679571+00:00
-- url     : https://prove2.me/submissions/3d206ba7-8eac-4539-a098-ec5d1eb09c78

-- Sol generated from MachineLearning/Neural/SubQuadraticAttention.lean
import Mathlib
import Definitions.Def_MachineLearning_Neural_SubQuadraticAttention

/-! # CatalogBuild.MachineLearning.Neural.SubQuadraticAttention

Auto-generated from theorem catalog database.
Domain: MachineLearning/Neural
Declarations: 16
-/


noncomputable section



/-- Block size is always positive. -/
theorem blockSize_pos (N : ℕ) : 0 < blockSize N := by simp [blockSize]































theorem solution(N : ℕ) (i : ℕ) :
    sparseAttendCount N i ≤ 2 * blockSize N := by
  -- The set of tokens that token i attends to in the sparse attention is a subset of those that are in the same block or in block 0.
  have h_subset : (Finset.range N).filter (fun j => (sparseAttentionMask N i j)) ⊆ ((Finset.range N).filter (fun j => blockIndex N i = blockIndex N j)) ∪ ((Finset.range N).filter (fun j => blockIndex N j = 0)) := by
    intro j hj; unfold sparseAttentionMask at hj; aesop;
  -- The set of tokens that are in the same block or in block 0 has cardinality at most 2 * blockSize N.
  have h_card : ((Finset.range N).filter (fun j => blockIndex N i = blockIndex N j)).card ≤ blockSize N ∧ ((Finset.range N).filter (fun j => blockIndex N j = 0)).card ≤ blockSize N := by
    constructor;
    · -- The set of tokens in the same block as i is a subset of the range N and has cardinality at most blockSize N.
      have h_same_block : ((Finset.range N).filter (fun j => blockIndex N i = blockIndex N j)).card ≤ Finset.card (Finset.Ico (blockIndex N i * blockSize N) ((blockIndex N i + 1) * blockSize N)) := by
        refine Finset.card_le_card ?_;
        intro j hj; simp_all +decide [ blockIndex ];
        exact ⟨ Nat.div_mul_le_self _ _, by linarith [ Nat.div_add_mod j ( blockSize N ), Nat.mod_lt j ( blockSize_pos N ) ] ⟩;
      simp_all +decide [ add_mul ];
    · -- The set of tokens that are in block 0 has cardinality at most blockSize N.
      have h_card_block0 : ((Finset.range N).filter (fun j => blockIndex N j = 0)).card ≤ Finset.card (Finset.range (blockSize N)) := by
        refine Finset.card_le_card ?_;
        exact fun x hx => Finset.mem_range.mpr <| Nat.lt_of_not_ge fun h => absurd ( Finset.mem_filter.mp hx |>.2 ) ( Nat.ne_of_gt <| Nat.div_pos h <| Nat.pos_of_ne_zero <| by rw [ blockSize ] ; positivity );
      aesop;
  exact le_trans ( Finset.card_le_card h_subset ) ( le_trans ( Finset.card_union_le _ _ ) ( by linarith ) )
