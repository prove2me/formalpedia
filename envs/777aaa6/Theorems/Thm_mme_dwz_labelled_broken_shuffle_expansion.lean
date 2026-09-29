-- Prove2me | Theorems.Thm_mme_dwz_labelled_broken_shuffle_expansion
-- name    : mme_dwz_labelled_broken_shuffle_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:24:37.504023+00:00
-- url     : https://prove2.me/theorems/53a696ba-e49b-4cb9-ada2-1e391e0f7a55
-- title:
--   A label-aligned automorphism realizes the exact shuffled nonhole-block sum
-- statement:
--   Let $D$ be a trilinear standard tensor with useful-block labels on a distinguished $Z$-basis. Let $S$ be the nonhole-label set of a broken copy, and suppose modewise automorphisms $F_0,F_1,F_2$ fix $D$ while moving every distinguished basis label by one permutation $\sigma$. Then there are modewise linear maps from the literal broken subtensor $D_S$ into $D$ whose tensor image is
--
--   $$
--   \sum_b \mathbf 1_{\sigma^{-1}(b)\in S}\,D_b,
--   $$
--
--   where $D_b$ is the singleton useful-block tensor at label $b$. Thus the broken copy is embedded as exactly the shuffled nonhole-block sum, with the inverse-membership convention required by the Hole Lemma's owner projection.
--
--   **Formalization Note** The theorem is stated on an opaque labelled-data bundle and returns the actual modewise maps, so it can be specialized without unfolding the fifteen-component standard tensor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially Claim 5.9's simultaneous embedding of broken copies into one standard tensor after a common shuffle, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
import Theorems.Thm_mme_dwz_labelled_automorphism_maps_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_labelled_broken_shuffle_expansion
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m)
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (F : ∀ i : Fin 3, D.X.V i ≃ₗ[K] D.X.V i)
    (hFtensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) D.X.t = D.X.t)
    (hFbasis : ∀ W : GroupedAllowedWords.{u} m,
      ∃ W' : GroupedAllowedWords.{u} m,
        F 2 (D.basis W) = D.basis W' ∧
          D.label W' = move (D.label W)) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    ∃ shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzLabelledUsefulBlockTensor K m D block
          else 0 := by
  sorry
