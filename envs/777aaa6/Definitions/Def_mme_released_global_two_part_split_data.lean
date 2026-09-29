-- Prove2me | Definitions.Def_mme_released_global_two_part_split_data
-- name    : mme_released_global_two_part_split_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T20:29:32.043794+00:00
-- url     : https://prove2.me/theorems/2e4d8b71-3338-40d7-a61d-3968afda52d7
-- title:
--   Two-part split of the released global candidate
-- statement:
--   Block regrouping of the released global candidate and its two-part split: fine positions as (block, letter) pairs, the block word and the cell of a block, the boundary cells (those with a zero grade in some physical mode) and the hashed cells, the position maps of the two parts, and the two part predicates QZero (exact grades and exact released histograms) and QPos (prescribed grades with per-cell frequencies within eps). Includes the lemma that the window condition of an orientation is equivalent to per-block grades plus per-cell block-word histograms.
-- source:
--   Assembly infrastructure for the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6) over the Duan-Wu-Zhou fourth-power construction (https://arxiv.org/html/2210.10173v5, section 7).

import Mathlib
import Definitions.Def_mme_released_global_joint_interface
import Theorems.Thm_mme_exact_profile_boundary_end
import Theorems.Thm_mme_released_global_physical_orientation
import Theorems.Thm_mme_released_global_joint_counts_valid
import Theorems.Thm_mme_released_global_supported_frame

open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RecursiveYZ.Boundary
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace MME.ReleasedRecursive.Asm

variable {k : ℕ}

/-- A global block: an owner and one of its blocks. -/
abbrev Blk (k : ℕ) := (o : Fin 6) × Fin (blocks k)

/-- The fine position of the `r`-th letter of a global block. -/
noncomputable def fine (k : ℕ) (b : Blk k) (r : Fin 4) : Fin (4 * (6 * blocks k)) :=
  jointPositions k ⟨b.1, Fin.cast (show blocks k * 4 = 4 * blocks k by omega) (finProdFinEquiv (b.2, r))⟩

/-- The letters of the blocks exhaust the fine positions. -/
noncomputable def fineEquiv (k : ℕ) : Blk k × Fin 4 ≃ Fin (4 * (6 * blocks k)) where
  toFun p := fine k p.1 p.2
  invFun z :=
    (⟨((jointPositions k).symm z).1,
      (finProdFinEquiv.symm (Fin.cast (show 4 * blocks k = blocks k * 4 by omega) ((jointPositions k).symm z).2)).1⟩,
      (finProdFinEquiv.symm (Fin.cast (show 4 * blocks k = blocks k * 4 by omega) ((jointPositions k).symm z).2)).2)
  left_inv := by
    rintro ⟨⟨o, b⟩, r⟩
    simp [fine]
  right_inv := by
    intro z
    simp only [fine, Prod.mk.eta, Equiv.apply_symm_apply, Fin.cast_trans, Fin.cast_eq_self,
      Sigma.eta, Equiv.symm_apply_apply]

/-- The complete level-3 word of a block. -/
noncomputable def blockWord (k : ℕ) (x : FineWord (4 * (6 * blocks k))) (b : Blk k) :
    CompleteWord 3 := fun r ↦ x (fine k b (Fin.cast (by norm_num) r))

/-- The hash cell of a block. -/
noncomputable def cellOf (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : Blk k) : Shape :=
  (a b.1).val 0 b.2

/-- Blocks whose cell has a zero coordinate go to the boundary. -/
def isZeroCell (c : Shape) : Prop := (c.val 0).val = 0 ∨ (c.val 1).val = 0 ∨ (c.val 2).val = 0

instance (c : Shape) : Decidable (isZeroCell c) := by unfold isZeroCell; infer_instance

/-- The word of a block, as the framework's block splitting sees it. -/
theorem split_blockWord (k : ℕ) (hk : 0 < k) (o : Fin 6) (a : ∀ o : Fin 6, Reference o k)
    (x : FineWord (4 * (6 * blocks k))) (b : Fin (blocks k)) :
    split (frame o k hk (a o)).positions (frame o k hk (a o)).length
      (fun r ↦ x (jointPositions k ⟨o, r⟩)) ((positions k) b) = blockWord k x ⟨o, b⟩ := by
  funext r
  simp only [split, blockWord, fine, Equiv.symm_apply_apply]
  congr 1

/-- The cell of a shape in the one-region global frame. -/
abbrev cellOfShape (c : Shape) : Cell 8 1 (fun _ _ ↦ 8) := ⟨0, c⟩

/-- Cell histograms of the global frame are block counts. -/
theorem count_blocks (k : ℕ) (hk : 0 < k) (o : Fin 6) (a : ∀ o : Fin 6, Reference o k)
    (x : FineWord (4 * (6 * blocks k))) (c : Shape) (w : CompleteWord 3) :
    count (GlobalCW.cell (frame o k hk (a o)).reference)
        (split (frame o k hk (a o)).positions (frame o k hk (a o)).length
          (fun r ↦ x (jointPositions k ⟨o, r⟩))) (cellOfShape c) w =
      Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c ∧ blockWord k x ⟨o, b⟩ = w} := by
  classical
  have hcell : ∀ b : Fin (blocks k),
      (GlobalCW.cell (frame o k hk (a o)).reference ((positions k) b) = cellOfShape c ↔
        (a o).val 0 b = c) := by
    intro b
    constructor
    · intro h
      have h2 := (Sigma.mk.inj_iff.mp h).2
      simpa [GlobalCW.cell, cellOfShape] using eq_of_heq h2
    · intro h
      simp only [GlobalCW.cell, cellOfShape]
      congr 1
  rw [Fintype.card_subtype]
  unfold count
  refine Finset.card_bij' (i := fun p _ ↦ (positions k).symm p) (j := fun b _ ↦ (positions k) b)
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hb := (positions k).apply_symm_apply p
    refine ⟨(hcell _).1 (by rw [hb]; exact hp.1), ?_⟩
    have := split_blockWord k hk o a x ((positions k).symm p)
    rw [hb] at this
    exact this.symm.trans hp.2
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨(hcell b).2 hb.1, (split_blockWord k hk o a x b).trans hb.2⟩
  · intro p _
    exact (positions k).apply_symm_apply p
  · intro b _
    exact (positions k).symm_apply_apply b

/-- One owner's window, in terms of its blocks. -/
theorem window_iff (k : ℕ) (hk : 0 < k) (o : Fin 6) (a : ∀ o : Fin 6, Reference o k) (eps : ℝ)
    (i : Fin 3) (x : FineWord (4 * (6 * blocks k))) :
    physicalWindow o k hk (a o) eps i (fun r ↦ x (jointPositions k ⟨o, r⟩)) ↔
      ((∀ b : Fin (blocks k),
          CWCells.grade (blockWord k x ⟨o, b⟩) = (((a o).val 0 b).val (hashMode o i)).val) ∧
        ∀ (c : Shape) (w : Word),
          |(Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c ∧ blockWord k x ⟨o, b⟩ = w} : ℝ) /
              (blocks k : ℝ) - (profile o).2 (hashMode o i) (cellOfShape c) w| ≤ eps) := by
  classical
  unfold physicalWindow physicalPredicate HistogramFrame.window
  constructor
  · rintro ⟨hgrade, hgood⟩
    refine ⟨fun b ↦ ?_, fun c w ↦ ?_⟩
    · have := hgrade ((positions k) b)
      rw [split_blockWord k hk o a x b] at this
      simpa [GlobalCW.cell] using this
    · have := hgood (cellOfShape c) w
      rwa [count_blocks k hk o a x c w] at this
  · rintro ⟨hgrade, hgood⟩
    constructor
    · intro p
      have hb := (positions k).apply_symm_apply p
      have hg := hgrade ((positions k).symm p)
      have hs := split_blockWord k hk o a x ((positions k).symm p)
      rw [hb] at hs
      rw [hs, hg, ← hb]
      rfl
    · rintro ⟨r, c⟩ w
      have hr : r = 0 := Fin.eq_zero r
      subst hr
      rw [count_blocks k hk o a x c w]
      exact hgood c w

/-! ### The two-part split of the blocks -/

/-- Blocks of boundary cells. -/
abbrev ZBlk (k : ℕ) (a : ∀ o : Fin 6, Reference o k) := {b : Blk k // isZeroCell (cellOf k a b)}

/-- Blocks of hashed cells. -/
abbrev PBlk (k : ℕ) (a : ∀ o : Fin 6, Reference o k) := {b : Blk k // ¬ isZeroCell (cellOf k a b)}

noncomputable def zCount (k : ℕ) (a : ∀ o : Fin 6, Reference o k) : ℕ := Fintype.card (ZBlk k a)

noncomputable def pCount (k : ℕ) (a : ∀ o : Fin 6, Reference o k) : ℕ := Fintype.card (PBlk k a)

/-- Sizes of the two parts, in fine positions. -/
noncomputable def partSize (k : ℕ) (a : ∀ o : Fin 6, Reference o k) : Fin 2 → ℕ :=
  ![4 * zCount k a, 4 * pCount k a]

theorem partSize_sum (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    partSize k a 0 + partSize k a 1 = 4 * (6 * blocks k) := by
  have h : zCount k a + pCount k a = Fintype.card (Blk k) := by
    unfold zCount pCount
    have h := Fintype.card_congr (Equiv.sumCompl (fun b : Blk k ↦ isZeroCell (cellOf k a b)))
    rw [Fintype.card_sum] at h
    exact h
  have hcard : Fintype.card (Blk k) = 6 * blocks k := by simp [Blk]
  simp only [partSize, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  omega

/-- A two-part sigma type is a sum. -/
def sigmaTwo (f : Fin 2 → ℕ) : ((j : Fin 2) × Fin (f j)) ≃ Fin (f 0) ⊕ Fin (f 1) where
  toFun p := match p with
    | ⟨0, i⟩ => Sum.inl i
    | ⟨1, i⟩ => Sum.inr i
  invFun q := match q with
    | Sum.inl i => ⟨0, i⟩
    | Sum.inr i => ⟨1, i⟩
  left_inv := by rintro ⟨j, i⟩; match j with | 0 => rfl | 1 => rfl
  right_inv := by rintro (i | i) <;> rfl

@[simp] theorem sigmaTwo_zero {f : Fin 2 → ℕ} (i : Fin (f 0)) :
    sigmaTwo f ⟨0, i⟩ = Sum.inl i := rfl

@[simp] theorem sigmaTwo_one {f : Fin 2 → ℕ} (i : Fin (f 1)) :
    sigmaTwo f ⟨1, i⟩ = Sum.inr i := rfl

/-- The fine positions of one part, as its blocks times four letters. -/
noncomputable def partBlocks (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    ((j : Fin 2) × Fin (partSize k a j)) ≃ (ZBlk k a × Fin 4) ⊕ (PBlk k a × Fin 4) :=
  (sigmaTwo (partSize k a)).trans
    (Equiv.sumCongr
      (((finCongr (show partSize k a 0 = zCount k a * 4 by simp [partSize]; ring)).trans
          finProdFinEquiv.symm).trans
        (Equiv.prodCongr (Fintype.equivFin (ZBlk k a)).symm (Equiv.refl (Fin 4))))
      (((finCongr (show partSize k a 1 = pCount k a * 4 by simp [partSize]; ring)).trans
          finProdFinEquiv.symm).trans
        (Equiv.prodCongr (Fintype.equivFin (PBlk k a)).symm (Equiv.refl (Fin 4)))))

/-- The positions of the two-part split. -/
noncomputable def partPositions (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    ((j : Fin 2) × Fin (partSize k a j)) ≃ Fin (4 * (6 * blocks k)) :=
  (partBlocks k a).trans
    (((Equiv.sumProdDistrib (ZBlk k a) (PBlk k a) (Fin 4)).symm.trans
      (Equiv.prodCongr (Equiv.sumCompl (fun b : Blk k ↦ isZeroCell (cellOf k a b)))
        (Equiv.refl (Fin 4)))).trans (fineEquiv k))

/-- The index of a letter of a block inside the two-part split. -/
noncomputable def partIdx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : Blk k) (r : Fin 4) :
    (j : Fin 2) × Fin (partSize k a j) :=
  (partPositions k a).symm (fine k b r)

theorem partPositions_idx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : Blk k) (r : Fin 4) :
    partPositions k a (partIdx k a b r) = fine k b r :=
  (partPositions k a).apply_symm_apply _

/-- Boundary blocks land in part zero, hashed blocks in part one. -/
theorem partIdx_fst (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : Blk k) (r : Fin 4) :
    (partIdx k a b r).1 = if isZeroCell (cellOf k a b) then 0 else 1 := by
  classical
  have hfe : (fineEquiv k).symm (fine k b r) = (b, r) := (fineEquiv k).symm_apply_apply (b, r)
  simp only [partIdx, partPositions, partBlocks, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl,
    id_eq, hfe]
  by_cases h : isZeroCell (cellOf k a b)
  · rw [if_pos h, Equiv.sumCompl_symm_apply_of_pos
      (p := fun b : Blk k ↦ isZeroCell (cellOf k a b)) (a := b) h]
    rfl
  · rw [if_neg h, Equiv.sumCompl_symm_apply_of_neg
      (p := fun b : Blk k ↦ isZeroCell (cellOf k a b)) (a := b) h]
    rfl

/-- The index of a letter of a boundary block inside part zero. -/
noncomputable def zIdx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : ZBlk k a) (r : Fin 4) :
    Fin (partSize k a 0) :=
  Fin.cast (by rw [partIdx_fst, if_pos b.property]) (partIdx k a b.val r).2

/-- The index of a letter of a hashed block inside part one. -/
noncomputable def pIdx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : PBlk k a) (r : Fin 4) :
    Fin (partSize k a 1) :=
  Fin.cast (by rw [partIdx_fst, if_neg b.property]) (partIdx k a b.val r).2

theorem sigma_cast {f : Fin 2 → ℕ} {j j' : Fin 2} (h : j = j') (i : Fin (f j)) :
    (⟨j', Fin.cast (congrArg f h) i⟩ : (j : Fin 2) × Fin (f j)) = ⟨j, i⟩ := by
  subst h
  rfl

theorem partPositions_zIdx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : ZBlk k a) (r : Fin 4) :
    partPositions k a ⟨0, zIdx k a b r⟩ = fine k b.val r := by
  have h : (partIdx k a b.val r).1 = 0 := by rw [partIdx_fst, if_pos b.property]
  have := sigma_cast (f := partSize k a) h (partIdx k a b.val r).2
  rw [show (⟨0, zIdx k a b r⟩ : (j : Fin 2) × Fin (partSize k a j)) = partIdx k a b.val r from this]
  exact partPositions_idx k a b.val r

theorem partPositions_pIdx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : PBlk k a) (r : Fin 4) :
    partPositions k a ⟨1, pIdx k a b r⟩ = fine k b.val r := by
  have h : (partIdx k a b.val r).1 = 1 := by rw [partIdx_fst, if_neg b.property]
  have := sigma_cast (f := partSize k a) h (partIdx k a b.val r).2
  rw [show (⟨1, pIdx k a b r⟩ : (j : Fin 2) × Fin (partSize k a j)) = partIdx k a b.val r from this]
  exact partPositions_idx k a b.val r

end MME.ReleasedRecursive.Asm

namespace MME.ReleasedRecursive.Asm

variable {k : ℕ}

/-- A boundary cell: an owner together with a shape having a zero coordinate. -/
abbrev ZCell := {p : Fin 6 × Shape // isZeroCell p.2}

noncomputable instance : Fintype ZCell := Subtype.fintype _

/-- The number of boundary cells. -/
noncomputable def zCells : ℕ := Fintype.card ZCell

noncomputable def zCellIdx : ZCell ≃ Fin zCells := Fintype.equivFin _

/-- The boundary cell of a boundary block. -/
noncomputable def cellOfZ (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (b : ZBlk k a) : ZCell :=
  ⟨(b.val.1, cellOf k a b.val), b.property⟩

/-- The enumeration of the boundary blocks used by the two-part split. -/
noncomputable def zEnum (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    ZBlk k a ≃ Fin (zCount k a) := Fintype.equivFin _

/-- Physical and hash modes correspond. -/
noncomputable def hashEquiv (o : Fin 6) : Fin 3 ≃ Fin 3 where
  toFun := hashMode o
  invFun := roles o
  left_inv i := (mme_released_global_physical_orientation.1 o i).1
  right_inv i := (mme_released_global_physical_orientation.1 o i).2

/-- The physical grade triple of a boundary cell. -/
noncomputable def zGrade (c : ZCell) (i : Fin 3) : ℕ := ((c.val.2).val (hashMode c.val.1 i)).val

/-- Some physical mode of a boundary cell has grade zero. -/
theorem zGrade_zero (c : ZCell) : ∃ i : Fin 3, zGrade c i = 0 := by
  have h := c.property
  unfold isZeroCell at h
  unfold zGrade
  rcases h with h | h | h
  · exact ⟨roles c.val.1 0, by rw [(mme_released_global_physical_orientation.1 c.val.1 0).2]; exact h⟩
  · exact ⟨roles c.val.1 1, by rw [(mme_released_global_physical_orientation.1 c.val.1 1).2]; exact h⟩
  · exact ⟨roles c.val.1 2, by rw [(mme_released_global_physical_orientation.1 c.val.1 2).2]; exact h⟩

/-- A chosen zero mode of a boundary cell. -/
noncomputable def zMode (c : ZCell) : Fin 3 := (zGrade_zero c).choose

theorem zMode_spec (c : ZCell) : zGrade c (zMode c) = 0 := (zGrade_zero c).choose_spec

/-- The grade triple of a boundary cell sums to eight. -/
theorem zGrade_total (c : ZCell) : zGrade c 0 + zGrade c 1 + zGrade c 2 = 2 * 2 ^ (3 - 1) := by
  have hsum := (c.val.2).property.1
  have hre : ∑ i : Fin 3, ((c.val.2).val (hashMode c.val.1 i)).val =
      ∑ j : Fin 3, ((c.val.2).val j).val :=
    Equiv.sum_comp (hashEquiv c.val.1) (fun j ↦ ((c.val.2).val j).val)
  simp only [Fin.sum_univ_three] at hre
  unfold zGrade
  omega

/-- The number of blocks of an owner in a given cell. -/
theorem block_count (k : ℕ) (o : Fin 6) (a : ∀ o : Fin 6, Reference o k) (c : Shape) :
    Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c} = counts o k 0 c := by
  classical
  have hmem := (a o).property
  simp only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have := hmem 0 c
  unfold RecursiveThinSplit.count at this
  rw [Fintype.card_subtype]
  exact this

/-- Mass, support and boundary profiles of the released scaled profile, for any scale. -/
theorem scaled_admissible_full (o : Fin 6) (k : ℕ) (hk : 0 < k) :
    (frame o k hk (mme_released_global_supported_frame o k hk).choose).Admissible
      (scaledWords o k) := (mme_released_global_supported_frame o k hk).choose_spec.1

theorem scaled_boundary (o : Fin 6) (k : ℕ) (hk : 0 < k) : BoundaryProfiles (scaledWords o k) :=
  (scaled_admissible_full o k hk).2.2

/-- In a cell with a zero grade, the other two modes' histograms are reflections. -/
theorem scaled_flip (o : Fin 6) (k : ℕ) (hk : 0 < k) (c : Cell 8 1 (fun _ _ ↦ 8))
    (j0 j1 j2 : Fin 3) (h0 : (c.2.val j0).val = 0) (h01 : j0 ≠ j1) (h02 : j0 ≠ j2)
    (h12 : j1 ≠ j2) (w : Word) :
    scaledWords o k j1 c w = scaledWords o k j2 c (fun r ↦ Fin.rev (w r)) := by
  obtain ⟨hb1, hb2, hb3⟩ := scaled_boundary o k hk
  have hrev : ∀ v : Word, (fun r ↦ Fin.rev (Fin.rev (v r))) = v := by
    intro v
    funext r
    simp
  match j0, j1, j2 with
  | 0, 0, 0 => exact absurd rfl h01
  | 0, 0, 1 => exact absurd rfl h01
  | 0, 0, 2 => exact absurd rfl h01
  | 0, 1, 0 => exact absurd rfl h02
  | 0, 1, 1 => exact absurd rfl h12
  | 0, 1, 2 => rw [hb2 c h0 (fun r ↦ Fin.rev (w r)), hrev]
  | 0, 2, 0 => exact absurd rfl h02
  | 0, 2, 1 => exact hb2 c h0 w
  | 0, 2, 2 => exact absurd rfl h12
  | 1, 0, 0 => exact absurd rfl h12
  | 1, 0, 1 => exact absurd rfl h02
  | 1, 0, 2 => rw [hb3 c h0 (fun r ↦ Fin.rev (w r)), hrev]
  | 1, 1, 0 => exact absurd rfl h01
  | 1, 1, 1 => exact absurd rfl h01
  | 1, 1, 2 => exact absurd rfl h01
  | 1, 2, 0 => exact hb3 c h0 w
  | 1, 2, 1 => exact absurd rfl h02
  | 1, 2, 2 => exact absurd rfl h12
  | 2, 0, 0 => exact absurd rfl h12
  | 2, 0, 1 => rw [hb1 c h0 (fun r ↦ Fin.rev (w r)), hrev]
  | 2, 0, 2 => exact absurd rfl h02
  | 2, 1, 0 => exact hb1 c h0 w
  | 2, 1, 1 => exact absurd rfl h12
  | 2, 1, 2 => exact absurd rfl h02
  | 2, 2, 0 => exact absurd rfl h01
  | 2, 2, 1 => exact absurd rfl h01
  | 2, 2, 2 => exact absurd rfl h01

/-- Mass and support of the released scaled profile, for any scale. -/
theorem scaled_admissible (o : Fin 6) (k : ℕ) (hk : 0 < k) :
    (∀ (i : Fin 3) (c : Cell 8 1 (fun _ _ ↦ 8)), ∑ w, scaledWords o k i c w = counts o k c.1 c.2) ∧
    (∀ (i : Fin 3) (c : Cell 8 1 (fun _ _ ↦ 8)) (w : Word),
      0 < scaledWords o k i c w → CWCells.grade w = (c.2.val i).val) := by
  obtain ⟨a, hadm, -⟩ := mme_released_global_supported_frame o k hk
  exact ⟨hadm.1, hadm.2.1⟩

/-- Boundary blocks of one cell are exactly that owner's blocks with that shape. -/
noncomputable def zFiber (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) :
    {b : ZBlk k a // cellOfZ k a b = C} ≃
      {b : Fin (blocks k) // (a C.val.1).val 0 b = C.val.2} where
  toFun b := ⟨b.val.val.2, by
    have h := b.property
    have h1 : b.val.val.1 = C.val.1 := congrArg (fun z : ZCell ↦ z.val.1) h
    have h2 : cellOf k a b.val.val = C.val.2 := congrArg (fun z : ZCell ↦ z.val.2) h
    unfold cellOf at h2
    rw [← h2, h1]⟩
  invFun b := ⟨⟨⟨C.val.1, b.val⟩, by
      show isZeroCell (cellOf k a ⟨C.val.1, b.val⟩)
      unfold cellOf
      simp only []
      rw [b.property]
      exact C.property⟩, by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show cellOf k a ⟨C.val.1, b.val⟩ = C.val.2
      unfold cellOf
      exact b.property⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    have h1 : b.val.val.1 = C.val.1 := congrArg (fun z : ZCell ↦ z.val.1) b.property
    show (⟨C.val.1, b.val.val.2⟩ : Blk k) = b.val.val
    rw [← h1]
  right_inv b := by
    apply Subtype.ext
    rfl

/-- The cell map of the boundary part. -/
noncomputable def zCellOf (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (q : Fin (zCount k a)) :
    Fin zCells := zCellIdx (cellOfZ k a ((zEnum k a).symm q))

/-- The zero mode of a boundary cell index. -/
noncomputable def zZero (c : Fin zCells) : Fin 3 := zMode (zCellIdx.symm c)

/-- The physical grades of a boundary cell index. -/
noncomputable def zGradeAt (c : Fin zCells) : Fin 3 → ℕ := zGrade (zCellIdx.symm c)

/-- The released histogram of a boundary cell index, in the mode after its zero mode. -/
noncomputable def zCountAt (k : ℕ) (c : Fin zCells) (w : Word) : ℕ :=
  scaledWords (zCellIdx.symm c).val.1 k
    (hashMode (zCellIdx.symm c).val.1 (zZero c + 1)) (cellOfShape (zCellIdx.symm c).val.2) w

/-- The exact all-mode profile of the boundary part. -/
noncomputable def zMu (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (i : Fin 3) (c : Fin zCells)
    (s : Word) : ℕ :=
  if i = zZero c then
    (if s = (fun _ ↦ 0) then Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c} else 0)
  else if i = zZero c + 1 then zCountAt k c s else zCountAt k c (Boundary.flipLabel s)

theorem zLen (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    zCount k a * 2 ^ (3 - 1) = partSize k a 0 := by
  simp only [partSize, Matrix.cons_val_zero]
  ring

/-- The boundary part's own block splitting agrees with the global blocks. -/
theorem partPositions_zblock (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (q : Fin (zCount k a))
    (r : Fin (2 ^ (3 - 1))) :
    partPositions k a ⟨0, Fin.cast (zLen k a) (finProdFinEquiv (q, r))⟩ =
      fine k ((zEnum k a).symm q).val (Fin.cast (by norm_num) r) := by
  simp only [partPositions, partBlocks, zEnum, Equiv.trans_apply, Equiv.coe_trans, sigmaTwo_zero,
    Equiv.sumCongr_apply, Sum.map_inl, finCongr_apply, Fin.cast_trans, Fin.cast_eq_self,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq, Equiv.symm_apply_apply,
    Equiv.sumProdDistrib_symm_apply_left, Equiv.sumCompl_apply_inl, Function.comp_apply]
  rfl

/-- The enumeration of the hashed blocks used by the two-part split. -/
noncomputable def pEnum (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    PBlk k a ≃ Fin (pCount k a) := Fintype.equivFin _

theorem pLen (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    pCount k a * 2 ^ (3 - 1) = partSize k a 1 := by
  show pCount k a * 4 = partSize k a 1
  simp only [partSize, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  ring

/-- The hashed part's own block splitting agrees with the global blocks. -/
theorem partPositions_pblock (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (q : Fin (pCount k a))
    (r : Fin (2 ^ (3 - 1))) :
    partPositions k a ⟨1, Fin.cast (pLen k a) (finProdFinEquiv (q, r))⟩ =
      fine k ((pEnum k a).symm q).val (Fin.cast (by norm_num) r) := by
  simp only [partPositions, partBlocks, pEnum, Equiv.trans_apply, Equiv.coe_trans, sigmaTwo_one,
    Equiv.sumCongr_apply, Sum.map_inr, finCongr_apply, Fin.cast_trans, Fin.cast_eq_self,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq, Equiv.symm_apply_apply,
    Equiv.sumProdDistrib_symm_apply_right, Equiv.sumCompl_apply_inr, Function.comp_apply]
  rfl

/-- The boundary part's predicate: exact grades and exact released histograms. -/
noncomputable def QZero (k : ℕ) (a : ∀ o : Fin 6, Reference o k) :
    Predicate (partSize k a 0) :=
  fun i x ↦
    (∀ p, CWCells.grade (split (Equiv.refl (Fin (zCount k a))) (zLen k a) x p) =
        zGradeAt (zCellOf k a p) i) ∧
      Useful (zCellOf k a) (zMu k a i) (split (Equiv.refl (Fin (zCount k a))) (zLen k a) x)

/-- The word of a hashed block inside the part word. -/
noncomputable def pBlockWord (k : ℕ) (a : ∀ o : Fin 6, Reference o k)
    (y : FineWord (partSize k a 1)) (b : PBlk k a) : Word :=
  fun r ↦ y (Fin.cast (pLen k a) (finProdFinEquiv (pEnum k a b, r)))

/-- The hashed part's predicate: correct grades and cell histograms inside the window. -/
noncomputable def QPos (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (i : Fin 3) (y : FineWord (partSize k a 1)) : Prop :=
  (∀ b : PBlk k a, CWCells.grade (pBlockWord k a y b) =
      ((cellOf k a b.val).val (hashMode b.val.1 i)).val) ∧
  ∀ (o : Fin 6) (c : Shape), ¬ isZeroCell c → ∀ w : Word,
    |(Fintype.card {b : PBlk k a // b.val.1 = o ∧ (a o).val 0 b.val.2 = c ∧
        pBlockWord k a y b = w} : ℝ) / (blocks k : ℝ) -
      (profile o).2 (hashMode o i) (cellOfShape c) w| ≤ eps o

/-- The word of a boundary block, from the part word. -/
theorem zWord (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (x : FineWord (4 * (6 * blocks k)))
    (q : Fin (zCount k a)) :
    (fun r ↦ (fun t ↦ x (partPositions k a ⟨0, t⟩)) (Fin.cast (zLen k a) (finProdFinEquiv (q, r)))) =
      blockWord k x ((zEnum k a).symm q).val := by
  funext r
  simp only [partPositions_zblock k a q r, blockWord]

/-- The word of a hashed block, from the part word. -/
theorem pWord (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (x : FineWord (4 * (6 * blocks k)))
    (b : PBlk k a) :
    pBlockWord k a (fun r ↦ x (partPositions k a ⟨1, r⟩)) b = blockWord k x b.val := by
  funext r
  unfold pBlockWord
  simp only [partPositions_pblock k a (pEnum k a b) r, Equiv.symm_apply_apply, blockWord]

/-- A boundary block of a given cell: its owner and its shape. -/
theorem zblk_of_cell (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) (b : ZBlk k a)
    (h : cellOfZ k a b = C) :
    (⟨C.val.1, b.val.2⟩ : Blk k) = b.val ∧ (a C.val.1).val 0 b.val.2 = C.val.2 := by
  have h1 : b.val.1 = C.val.1 := congrArg (fun z : ZCell ↦ z.val.1) h
  have h2 : cellOf k a b.val = C.val.2 := congrArg (fun z : ZCell ↦ z.val.2) h
  have hb : (⟨C.val.1, b.val.2⟩ : Blk k) = b.val := Sigma.ext h1.symm HEq.rfl
  refine ⟨hb, ?_⟩
  show cellOf k a (⟨C.val.1, b.val.2⟩ : Blk k) = C.val.2
  exact (congrArg (fun z ↦ cellOf k a z) hb).trans h2

/-- A block of a boundary cell is a boundary block. -/
theorem zblk_mk (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) (b : Fin (blocks k))
    (hb : (a C.val.1).val 0 b = C.val.2) : isZeroCell (cellOf k a ⟨C.val.1, b⟩) := by
  unfold cellOf
  simp only []
  rw [hb]
  exact C.property

theorem zblk_cellOfZ (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) (b : Fin (blocks k))
    (hb : (a C.val.1).val 0 b = C.val.2) :
    cellOfZ k a ⟨⟨C.val.1, b⟩, zblk_mk k a C b hb⟩ = C := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show cellOf k a ⟨C.val.1, b⟩ = C.val.2
    unfold cellOf
    exact hb

/-- The boundary block of a cell with a given shape. -/
noncomputable def mkZBlk (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) (b : Fin (blocks k))
    (hb : (a C.val.1).val 0 b = C.val.2) : ZBlk k a :=
  ⟨⟨C.val.1, b⟩, zblk_mk k a C b hb⟩

/-- Boundary blocks of one cell with a given word: counted inside the part or globally. -/
theorem zCount_eq (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell)
    (x : FineWord (4 * (6 * blocks k))) (w : Word) :
    Fintype.card {q : Fin (zCount k a) // cellOfZ k a ((zEnum k a).symm q) = C ∧
        blockWord k x ((zEnum k a).symm q).val = w} =
      Fintype.card {b : Fin (blocks k) // (a C.val.1).val 0 b = C.val.2 ∧
        blockWord k x ⟨C.val.1, b⟩ = w} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  refine Finset.card_bij' (i := fun q _ ↦ ((zEnum k a).symm q).val.2)
    (j := fun b hb ↦ zEnum k a (mkZBlk k a C b (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb.1))) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨(zblk_of_cell k a C _ hq.1).2,
      (congrArg (fun z ↦ blockWord k x z) (zblk_of_cell k a C _ hq.1).1).trans hq.2⟩
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [Equiv.symm_apply_apply]
    exact ⟨zblk_cellOfZ k a C b hb.1, hb.2⟩
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have heq : mkZBlk k a C ((zEnum k a).symm q).val.2 (zblk_of_cell k a C _ hq.1).2 =
        (zEnum k a).symm q := Subtype.ext (zblk_of_cell k a C _ hq.1).1
    exact (congrArg (zEnum k a) heq).trans ((zEnum k a).apply_symm_apply q)
  · intro b hb
    simp only [Equiv.symm_apply_apply]
    rfl

/-- Hashed blocks of one cell with a given word: counted inside the part or globally. -/
theorem pCount_eq (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (o : Fin 6) (c : Shape)
    (hc : ¬ isZeroCell c) (x : FineWord (4 * (6 * blocks k))) (w : Word) :
    Fintype.card {b : PBlk k a // b.val.1 = o ∧ (a o).val 0 b.val.2 = c ∧
        blockWord k x b.val = w} =
      Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c ∧ blockWord k x ⟨o, b⟩ = w} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  refine Finset.card_bij' (i := fun b _ ↦ b.val.2) (j := fun b hb ↦ (⟨⟨o, b⟩, by
      show ¬ isZeroCell (cellOf k a ⟨o, b⟩)
      unfold cellOf
      simp only []
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [hb.1]
      exact hc⟩ : PBlk k a)) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    have hsig : (⟨o, b.val.2⟩ : Blk k) = b.val := Sigma.ext hb.1.symm HEq.rfl
    exact ⟨hb.2.1, (congrArg (fun z ↦ blockWord k x z) hsig).trans hb.2.2⟩
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Subtype.ext (Sigma.ext hb.1.symm HEq.rfl)
  · intro b hb
    rfl

theorem zZero_idx (C : ZCell) : zZero (zCellIdx C) = zMode C := by
  unfold zZero
  rw [zCellIdx.symm_apply_apply]

theorem zGradeAt_idx (C : ZCell) (i : Fin 3) : zGradeAt (zCellIdx C) i = zGrade C i := by
  unfold zGradeAt
  rw [zCellIdx.symm_apply_apply]

theorem zCountAt_idx (k : ℕ) (C : ZCell) (w : Word) :
    zCountAt k (zCellIdx C) w =
      scaledWords C.val.1 k (hashMode C.val.1 (zMode C + 1)) (cellOfShape C.val.2) w := by
  unfold zCountAt
  rw [zZero_idx C, zCellIdx.symm_apply_apply]

theorem zCellOf_apply (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (q : Fin (zCount k a)) :
    zCellOf k a q = zCellIdx (cellOfZ k a ((zEnum k a).symm q)) := rfl

/-- The blocks of a boundary cell are exactly the released count of that cell. -/
theorem zFiber_idx (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) :
    Fintype.card {p : Fin (zCount k a) // zCellOf k a p = zCellIdx C} =
      counts C.val.1 k 0 C.val.2 := by
  classical
  have hfib : Fintype.card {q : Fin (zCount k a) // zCellOf k a q = zCellIdx C} =
      Fintype.card {b : Fin (blocks k) // (a C.val.1).val 0 b = C.val.2} := by
    refine Fintype.card_congr ((Equiv.subtypeEquiv (zEnum k a).symm ?_).trans (zFiber k a C))
    intro q
    exact ⟨fun h ↦ zCellIdx.injective h, fun h ↦ congrArg zCellIdx h⟩
  rw [hfib, block_count k C.val.1 a C.val.2]

/-- The boundary histograms have the right total. -/
theorem zCount_total (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) (c : Fin zCells) :
    ∑ s, zCountAt k c s = Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c} := by
  classical
  obtain ⟨C, rfl⟩ : ∃ C, zCellIdx C = c := ⟨zCellIdx.symm c, zCellIdx.apply_symm_apply c⟩
  rw [zFiber_idx k a C, Finset.sum_congr rfl (fun s _ ↦ zCountAt_idx k C s)]
  exact (scaled_admissible C.val.1 k hk).1 _ _

/-- The boundary histograms are supported on words of the right grade. -/
theorem zCount_support (k : ℕ) (hk : 0 < k) (c : Fin zCells) (s : Word) (hs : zCountAt k c s ≠ 0) :
    CWCells.grade s = zGradeAt c (zZero c + 1) := by
  obtain ⟨C, rfl⟩ : ∃ C, zCellIdx C = c := ⟨zCellIdx.symm c, zCellIdx.apply_symm_apply c⟩
  rw [zGradeAt_idx C, zZero_idx C] at *
  rw [zCountAt_idx k C s] at hs
  exact (scaled_admissible C.val.1 k hk).2 _ _ s (Nat.pos_of_ne_zero hs)

theorem flipLabel_eq (w : Word) : Boundary.flipLabel w = fun r ↦ Fin.rev (w r) := by
  funext r
  apply Fin.ext
  simp [Boundary.flipLabel, Fin.rev]

theorem grade_zero_word (w : Word) (h : CWCells.grade w = 0) : w = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp h r (Finset.mem_univ r)
  simpa using this

/-- In the zero mode, the released histogram is concentrated on the constant word. -/
theorem scaled_zero_mode (o : Fin 6) (k : ℕ) (hk : 0 < k) (c : Cell 8 1 (fun _ _ ↦ 8)) (j : Fin 3)
    (hj : (c.2.val j).val = 0) (w : Word) :
    scaledWords o k j c w = if w = (fun _ ↦ 0) then counts o k c.1 c.2 else 0 := by
  classical
  have hsupp := (scaled_admissible o k hk).2 j c
  have hmass := (scaled_admissible o k hk).1 j c
  have hzero : ∀ v : Word, v ≠ (fun _ ↦ 0) → scaledWords o k j c v = 0 := by
    intro v hv
    by_contra hne
    exact hv (grade_zero_word v (by rw [hsupp v (Nat.pos_of_ne_zero hne)]; exact hj))
  by_cases hw : w = (fun _ ↦ 0)
  · rw [if_pos hw, hw]
    rw [Finset.sum_eq_single (fun _ ↦ (0 : Fin 3)) (fun v _ hv ↦ hzero v hv)
      (fun h ↦ absurd (Finset.mem_univ _) h)] at hmass
    exact hmass
  · rw [if_neg hw]
    exact hzero w hw

attribute [local irreducible] zCellIdx zEnum

/-- The boundary profile of a cell is the released scaled histogram, in every mode. -/
theorem zMu_eq (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) (C : ZCell) (i : Fin 3)
    (w : Word) :
    zMu k a i (zCellIdx C) w =
      scaledWords C.val.1 k (hashMode C.val.1 i) (cellOfShape C.val.2) w := by
  classical
  unfold zMu
  rw [zZero_idx C]
  by_cases h1 : i = zMode C
  · rw [if_pos h1, zFiber_idx k a C,
      scaled_zero_mode C.val.1 k hk (cellOfShape C.val.2) (hashMode C.val.1 i)
        (by rw [h1]; exact zMode_spec C) w]
  · rw [if_neg h1]
    by_cases h2 : i = (zMode C + 1)
    · subst h2
      rw [if_pos rfl, zCountAt_idx k C]
    · rw [if_neg h2, zCountAt_idx k C, flipLabel_eq]
      have hz : ((C.val.2).val (hashMode C.val.1 (zMode C))).val = 0 := zMode_spec C
      have hne1 : hashMode C.val.1 (zMode C) ≠ hashMode C.val.1 i :=
        fun h ↦ h1 ((hashEquiv C.val.1).injective h).symm
      have hne2 : hashMode C.val.1 (zMode C) ≠
          hashMode C.val.1 ((zMode C + 1)) := by
        intro h
        have hzz := (hashEquiv C.val.1).injective h
        have hval : (zMode C).val = ((zMode C) + 1).val := congrArg Fin.val hzz
        simp only [Fin.add_def, Fin.val_one] at hval
        omega
      have hne3 : hashMode C.val.1 i ≠
          hashMode C.val.1 ((zMode C + 1)) :=
        fun h ↦ h2 ((hashEquiv C.val.1).injective h)
      exact (scaled_flip C.val.1 k hk (cellOfShape C.val.2) (hashMode C.val.1 (zMode C))
        (hashMode C.val.1 i) (hashMode C.val.1 ((zMode C + 1)))
        hz hne1 hne2 hne3 w).symm

end MME.ReleasedRecursive.Asm


