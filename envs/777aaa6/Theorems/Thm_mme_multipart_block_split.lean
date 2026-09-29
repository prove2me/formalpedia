-- Prove2me | Theorems.Thm_mme_multipart_block_split
-- name    : mme_multipart_block_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:57:44.093612+00:00
-- url     : https://prove2.me/theorems/ff4c8315-0638-45e7-950a-450f566fc037
-- title:
--   A p-part block split covers every block once and keeps a block's letters together
-- statement:
--   Blocks are the unit of position bookkeeping: a word lives on fine positions, every block owns a
--   fixed number of consecutive letters, and a recipe stage hands each of its parts a contiguous index
--   set that must be read as whole blocks. This is that bookkeeping, for an arbitrary number of parts
--   and an arbitrary assignment of blocks to parts.
--
--   Fix a finite type of blocks, a number of letters per block, an assignment of each block to one of
--   the parts, and an identification of block-letter pairs with the fine positions. Let the count of a
--   part be the number of blocks assigned to it, and its size the count times the number of letters.
--   Then:
--
--   - the counts add up to the number of blocks, and the sizes add up to the number of fine positions;
--   - listing the parts' blocks part by part is a bijection with the blocks, so the assignment covers
--     every block exactly once, and a part draws only blocks assigned to it;
--   - inside a part the positions are block-major: the letter of the part's own block is the same fine
--     position as the corresponding letter of that block seen globally, so all the letters of a block
--     stay together in one part, and the word a part reads off one of its blocks is the word the whole
--     reads off that block;
--   - every global position is accounted for, in the part its block was assigned to.
--
--   Nothing is assumed about the assignment. A part may be empty, and the blocks a part draws need not
--   form a contiguous range in any enumeration of the blocks — a part may take a prescribed number of
--   blocks from each of many cells, which is what a stage over several regions needs.
-- source:
--   Position bookkeeping for the regional constructions of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6, and of the Duan-Wu-Zhou fourth-power recursion (https://arxiv.org/abs/2210.10173), section 7. A generic combinatorial statement about splitting blocks into parts; no exponent claim.

import Mathlib
import Definitions.Def_mme_multipart_block_split_data

open BigOperators MME.MultiSplit
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

theorem mme_multipart_block_split :
    ∀ {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (len N : ℕ)
      (pos : B × Fin len ≃ Fin N),
      ((∑ j, multiCount part j) = Fintype.card B) ∧
      ((∑ j, multiSize len part j) = N) ∧
      (∀ (j : Fin p) (q : Fin (multiCount part j)),
        multiBlocks part ⟨j, q⟩ = ((multiEnum part j).symm q).val ∧
          part ((multiEnum part j).symm q).val = j) ∧
      Function.Bijective (multiBlocks part) ∧
      (∀ b : B, (multiBlocks part).symm b = ⟨part b, multiIdx part b⟩) ∧
      (∀ (j : Fin p) (q : Fin (multiCount part j)) (r : Fin len),
        multiPositions len part pos ⟨j, Fin.cast (multiLen len part j) (finProdFinEquiv (q, r))⟩ =
          pos (((multiEnum part j).symm q).val, r)) ∧
      (∀ (b : B) (r : Fin len),
        multiPositions len part pos ⟨part b, Fin.cast (multiLen len part (part b))
            (finProdFinEquiv (multiIdx part b, r))⟩ = pos (b, r)) ∧
      (∀ z : Fin N, (multiPositions len part pos).symm z =
        ⟨part (pos.symm z).1, Fin.cast (multiLen len part (part (pos.symm z).1))
          (finProdFinEquiv (multiIdx part (pos.symm z).1, (pos.symm z).2))⟩) ∧
      ∀ {A : Type v} (x : Fin N → A) (j : Fin p) (q : Fin (multiCount part j)),
        (fun r ↦ (fun t ↦ x (multiPositions len part pos ⟨j, t⟩))
            (Fin.cast (multiLen len part j) (finProdFinEquiv (q, r)))) =
          fun r ↦ x (pos (((multiEnum part j).symm q).val, r)) := by sorry
