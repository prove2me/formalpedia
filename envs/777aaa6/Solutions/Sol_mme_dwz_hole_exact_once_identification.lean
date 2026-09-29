-- Prove2me | solution 1 for mme_dwz_hole_exact_once_identification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:39:01.140046+00:00
-- url     : https://prove2.me/submissions/ef5ea3a0-ac9c-408b-816b-ca3384f73e61

import Mathlib.Tactic
import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_bigAdd_map_sum_restrict

/-!
# Exact-once ownership after the DWZ Hole-Lemma cover

This is the algebraic/combinatorial sentence in the last paragraph of the
proof of Duan--Wu--Zhou Lemma 5.6.  Once the shuffled non-hole sets cover all
available small Z-blocks, choose one surviving copy for each block, zero that
block in all other copies, and then identify the copies.  Every target block
tensor is consequently added exactly once.
-/

open BigOperators Finset
open MME MME.DWZSquare PiTensorProduct

universe u v

theorem solution
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
            TensorObj K d))) := by
  classical
  let owner : Block → Fin s := fun block ↦ Classical.choose (hcover block)
  have howner : ∀ block : Block,
      (system.move (shuffles (owner block))).symm block ∈
        (copies (owner block)).nonholes := by
    intro block
    exact Classical.choose_spec (hcover block)
  have hexact :
      (∑ t : Fin s, ∑ block : Block,
          if t = owner block then blockTensor block else 0) =
        ∑ block : Block, blockTensor block := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro block hblock
    simp
  refine ⟨owner, howner, hexact, ?_⟩
  let kept : Fin s → TensorObj K d := fun t =>
    { V := W
      t := ∑ block : Block,
        if t = owner block then blockTensor block else 0 }
  have hrestrict := mme_bigAdd_map_sum_restrict kept
    (fun _ _ => LinearMap.id)
  have hmapped :
      (∑ t : Fin s,
        PiTensorProduct.map (fun _ : Fin d => LinearMap.id) (kept t).t) =
      ∑ block : Block, blockTensor block := by
    simpa only [PiTensorProduct.map_id, kept] using hexact
  simpa only [hmapped, kept] using hrestrict
