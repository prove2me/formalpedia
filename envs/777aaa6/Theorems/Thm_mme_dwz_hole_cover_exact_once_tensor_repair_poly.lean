-- Prove2me | Theorems.Thm_mme_dwz_hole_cover_exact_once_tensor_repair_poly
-- name    : mme_dwz_hole_cover_exact_once_tensor_repair_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:23:35.25977+00:00
-- url     : https://prove2.me/theorems/529ad783-6ac4-48e8-93dd-760f0405938f
-- title:
--   Universe-polymorphic exact-once tensor repair from a Hole-Lemma cover
-- statement:
--   Let a finite family of broken tensor copies satisfy the quantitative hypotheses of the DWZ Hole Lemma, and suppose an available-block shuffle system acts uniformly on the finite block set. Assume moreover that, for every chosen shuffle family and every valid owner assignment, concrete modewise maps realize in copy $t$ precisely the target blocks owned by $t$. Then there are shuffles, an owner assignment, and modewise maps such that every block is covered and
--
--   $$
--   \sum_t\sum_b \mathbf 1_{\{t=\operatorname{owner}(b)\}}T_b=\sum_b T_b.
--   $$
--
--   Consequently, the direct sum of the broken source tensors restricts to the complete sum of target block tensors. The theorem returns the selected shuffles and all exact per-copy tensor equations in addition to the restriction.
--
--   **Formalization Note** The block-label type may inhabit a universe independent of the scalar field and target vector spaces, allowing finite DWZ combinatorial labels over an arbitrary field.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 5.6 and Claim 5.9, exact-once assembly of shuffled broken tensors; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_hole_lemma_cover_core
import Theorems.Thm_mme_bigAdd_map_sum_restrict

open BigOperators Finset
open MME MME.DWZSquare PiTensorProduct

universe u v w

set_option autoImplicit false

theorem mme_dwz_hole_cover_exact_once_tensor_repair_poly
    {K : Type u} [Field K]
    {s : ℕ}
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    {Block : Type w} {Shuffle : Type v}
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
