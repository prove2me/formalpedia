-- Prove2me | Theorems.Thm_mme_dwz_hole_cover_exact_once_tensor_repair
-- name    : mme_dwz_hole_cover_exact_once_tensor_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:15:51.707367+00:00
-- url     : https://prove2.me/theorems/c506d43b-fe68-4ba6-8d71-2d39c3cc7726
-- title:
--   Exact-once tensor repair from a DWZ Hole-Lemma cover
-- statement:
--   For a finite available-block shuffle system and a family of broken copies satisfying the DWZ Hole-Lemma cardinal and nonhole-fraction hypotheses, suppose each covered owner assignment is realized by actual modewise linear maps. The maps agree with the prescribed shuffle maps on X and Y, and the mapped tensor of copy t is exactly the sum of blocks uniquely owned by t. Then one can choose shuffles, owners, and maps for which the complete standard block sum is a genuine tensor restriction of the direct sum of broken sources. Each block occurs exactly once, so neither monomials nor shared X/Y spaces are duplicated.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 5.6 and the exact-once zeroing/identification step following Claims 5.8–5.10.

import Theorems.Thm_mme_dwz_hole_lemma_cover_core
import Theorems.Thm_mme_bigAdd_map_sum_restrict

open BigOperators Finset
open MME MME.DWZSquare PiTensorProduct

universe u v

set_option autoImplicit false

theorem mme_dwz_hole_cover_exact_once_tensor_repair
    {K : Type u} [Field K]
    {s : ℕ}
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (N ell : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t))
    (source : Fin s → TensorObj K 3)
    (blockTensor : Block → PiTensorProduct K W)
    (shuffleMap : (Fin s → Shuffle) →
      ∀ t i, (source t).V i →ₗ[K] W i)
    (realizeOwned :
      ∀ (shuffles : Fin s → Shuffle) (owner : Block → Fin s),
        (∀ block : Block,
          (system.move (shuffles (owner block))).symm block ∈
            (copies (owner block)).nonholes) →
        ∃ f : ∀ t i, (source t).V i →ₗ[K] W i,
          (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
          (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
          ∀ t,
            PiTensorProduct.map (f t) (source t).t =
              ∑ block : Block,
                if t = owner block then blockTensor block else 0) :
    ∃ (shuffles : Fin s → Shuffle) (owner : Block → Fin s)
        (f : ∀ t i, (source t).V i →ₗ[K] W i),
      (∀ block : Block, ∃ t : Fin s,
        (system.move (shuffles t)).symm block ∈ (copies t).nonholes) ∧
      (∀ block : Block,
        (system.move (shuffles (owner block))).symm block ∈
          (copies (owner block)).nonholes) ∧
      (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
      (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
      (∀ t,
        PiTensorProduct.map (f t) (source t).t =
          ∑ block : Block,
            if t = owner block then blockTensor block else 0) ∧
      TensorObj.Restrict
        ({ V := W
           t := ∑ block : Block, blockTensor block } : TensorObj K 3)
        (TensorObj.bigAdd source) := by
  sorry
