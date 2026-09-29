-- Prove2me | Theorems.Thm_mme_dwz_hole_exact_once_identification
-- name    : mme_dwz_hole_exact_once_identification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:38:25.396651+00:00
-- url     : https://prove2.me/theorems/19514989-2df9-4942-bb6d-ebdcd54abeb8
-- title:
--   DWZ Hole repair: exact-once zeroing and identification
-- statement:
--   Assume that chosen shuffles of finitely many broken copies cover every available small Z-block: for each target block, at least one shuffled copy contains its inverse image as a non-hole. For an arbitrary tensor contribution attached to each block, one can choose a single owner copy for every block so that (i) the owner really contains that block, (ii) zeroing the block in every non-owner copy makes the sum over copies exactly the complete block-tensor sum, with every contribution occurring once, and (iii) the complete tensor is an ordinary restriction of the direct sum of these post-zeroing copies via identification. This is the exact-once zeroing-and-gluing paragraph at the end of the proof of the Hole Lemma. It does not yet construct the concrete standard-form shuffle automorphisms or block projections.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, proof of Lemma 5.6, PDF pp. 49-50 / printed pp. 48-49; identification is defined in Section 3.2, PDF p. 18 / printed p. 17.

import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_bigAdd_map_sum_restrict
open BigOperators Finset
open MME MME.DWZSquare PiTensorProduct
universe u v

theorem mme_dwz_hole_exact_once_identification
    {K : Type u} [Field K]
    {d s : ℕ}
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block]
    [Fintype Shuffle] [DecidableEq Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (copies : Fin s → BrokenBlockCopy Block)
    (shuffles : Fin s → Shuffle)
    (hcover : ∀ block : Block, ∃ t : Fin s,
      (system.move (shuffles t)).symm block ∈ (copies t).nonholes)
    (blockTensor : Block → PiTensorProduct K W) :
    ∃ owner : Block → Fin s,
      (∀ block : Block,
        (system.move (shuffles (owner block))).symm block ∈
          (copies (owner block)).nonholes) ∧
      (∑ t : Fin s, ∑ block : Block,
          if t = owner block then blockTensor block else 0) =
        ∑ block : Block, blockTensor block ∧
      TensorObj.Restrict
        ({ V := W
           t := ∑ block : Block, blockTensor block } : TensorObj K d)
        (TensorObj.bigAdd (fun t : Fin s =>
          ({ V := W
             t := ∑ block : Block,
               if t = owner block then blockTensor block else 0 } :
            TensorObj K d))) := by sorry
