-- Prove2me | solution 1 for mme_multipart_block_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:57:54.329592+00:00
-- url     : https://prove2.me/submissions/6495f875-847e-43e7-be8b-2c53c81e9403

import Mathlib
import Definitions.Def_mme_multipart_block_split_data

open BigOperators MME.MultiSplit
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v


universe w

namespace MME.MultiSplit

@[simp] theorem sigmaCongrU_apply {I : Type w} {F : I → Type u} {G : I → Type v}
    (e : ∀ i, F i ≃ G i) (i : I) (x : F i) : sigmaCongrU e ⟨i, x⟩ = ⟨i, e i x⟩ := rfl

@[simp] theorem prodCongrU_apply {A : Type u} {C : Type v} (D : Type w) (e : A ≃ C) (x : A)
    (y : D) : prodCongrU D e (x, y) = (e x, y) := rfl

variable {p : ℕ} {B : Type u} [Fintype B]

@[simp] theorem multiBlocks_apply (part : B → Fin p) (j : Fin p) (q : Fin (multiCount part j)) :
    multiBlocks part ⟨j, q⟩ = ((multiEnum part j).symm q).val := rfl

@[simp] theorem multiBlocks_symm_apply (part : B → Fin p) (b : B) :
    (multiBlocks part).symm b = ⟨part b, multiIdx part b⟩ := rfl

/-- Part `j` draws only blocks assigned to `j`. -/
theorem multiEnum_part (part : B → Fin p) (j : Fin p) (q : Fin (multiCount part j)) :
    part ((multiEnum part j).symm q).val = j := ((multiEnum part j).symm q).property

/-- A block's index inside its own part names the block again. -/
theorem multiEnum_symm_idx (part : B → Fin p) (b : B) :
    ((multiEnum part (part b)).symm (multiIdx part b)).val = b := by
  simp only [multiIdx, Equiv.symm_apply_apply]

/-- The parts partition the blocks: the fibre counts add up to the number of blocks. -/
theorem multiCount_sum (part : B → Fin p) : (∑ j, multiCount part j) = Fintype.card B := by
  simpa using Fintype.card_congr (multiBlocks part)

/-- A part-local block's letters are the corresponding global block's letters. -/
theorem multiPositions_block {N : ℕ} (len : ℕ) (part : B → Fin p) (pos : B × Fin len ≃ Fin N)
    (j : Fin p) (q : Fin (multiCount part j)) (r : Fin len) :
    multiPositions len part pos ⟨j, Fin.cast (multiLen len part j) (finProdFinEquiv (q, r))⟩ =
      pos (((multiEnum part j).symm q).val, r) := by
  simp only [multiPositions, multiSplitPos, Equiv.trans_apply, sigmaCongrU_apply, finCongr_apply,
    Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply, Equiv.sigmaProdDistrib_symm_apply,
    prodCongrU_apply, multiBlocks_apply]

/-- Every block is reached, in the part it is assigned to. -/
theorem multiPositions_of_block {N : ℕ} (len : ℕ) (part : B → Fin p)
    (pos : B × Fin len ≃ Fin N) (b : B) (r : Fin len) :
    multiPositions len part pos
        ⟨part b, Fin.cast (multiLen len part (part b))
          (finProdFinEquiv (multiIdx part b, r))⟩ = pos (b, r) := by
  rw [multiPositions_block, multiEnum_symm_idx]

/-- The sizes of the parts add up to the number of fine positions. -/
theorem multiSize_sum {N : ℕ} (len : ℕ) (part : B → Fin p) (pos : B × Fin len ≃ Fin N) :
    (∑ j, multiSize len part j) = N := by
  simpa using Fintype.card_congr (multiPositions len part pos)

/-- Where a global position sits in the split. -/
theorem multiPositions_symm {N : ℕ} (len : ℕ) (part : B → Fin p) (pos : B × Fin len ≃ Fin N)
    (z : Fin N) :
    (multiPositions len part pos).symm z =
      ⟨part (pos.symm z).1, Fin.cast (multiLen len part (part (pos.symm z).1))
        (finProdFinEquiv (multiIdx part (pos.symm z).1, (pos.symm z).2))⟩ := by
  rw [Equiv.symm_apply_eq, multiPositions_of_block]
  simp

/-- The word a part reads off one of its blocks is the word the whole reads off that block. -/
theorem multiPositions_word {N : ℕ} {A : Type v} (len : ℕ) (part : B → Fin p)
    (pos : B × Fin len ≃ Fin N) (x : Fin N → A) (j : Fin p) (q : Fin (multiCount part j)) :
    (fun r ↦ (fun t ↦ x (multiPositions len part pos ⟨j, t⟩))
        (Fin.cast (multiLen len part j) (finProdFinEquiv (q, r)))) =
      fun r ↦ x (pos (((multiEnum part j).symm q).val, r)) := by
  funext r
  dsimp only
  rw [multiPositions_block]

end MME.MultiSplit


theorem solution :
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
          fun r ↦ x (pos (((multiEnum part j).symm q).val, r)) :=
  fun {B} _ {p} part len N pos ↦
    ⟨MME.MultiSplit.multiCount_sum part,
     MME.MultiSplit.multiSize_sum len part pos,
     fun j q ↦ ⟨MME.MultiSplit.multiBlocks_apply part j q, MME.MultiSplit.multiEnum_part part j q⟩,
     (multiBlocks part).bijective,
     fun b ↦ MME.MultiSplit.multiBlocks_symm_apply part b,
     fun j q r ↦ MME.MultiSplit.multiPositions_block len part pos j q r,
     fun b r ↦ MME.MultiSplit.multiPositions_of_block len part pos b r,
     fun z ↦ MME.MultiSplit.multiPositions_symm len part pos z,
     fun {A} x j q ↦ MME.MultiSplit.multiPositions_word len part pos x j q⟩
