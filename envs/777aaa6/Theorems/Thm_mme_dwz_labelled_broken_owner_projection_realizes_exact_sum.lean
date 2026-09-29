-- Prove2me | Theorems.Thm_mme_dwz_labelled_broken_owner_projection_realizes_exact_sum
-- name    : mme_dwz_labelled_broken_owner_projection_realizes_exact_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:00:55.23389+00:00
-- url     : https://prove2.me/theorems/15ed41b8-58a7-4be4-8564-2e0cefda7758
-- title:
--   Owner-selecting Z projection realizes the exact owned block sum in arbitrary labelled standard data
-- statement:
--   Let $D$ be trilinear standard data with a distinguished labelled basis in its $Z$ mode, and let $D_S$ be the literal subtensor retaining exactly a broken copy's nonhole label set $S$. Suppose modewise shuffle maps realize
--
--   $$
--   D_S \longmapsto \sum_b \mathbf 1_{\sigma^{-1}(b)\in S} D_b,
--   $$
--
--   where $D_b$ is the singleton tensor contribution with label $b$. Assign every target block $b$ to an owner copy $\operatorname{owner}(b)$, and assume that every block assigned to copy $t$ is present after that copy's shuffle. Then one may postcompose only the $Z$ map with a diagonal basis projection so that the resulting maps agree with the original shuffle maps on $X$ and $Y$ and satisfy
--
--   $$
--   D_S \longmapsto \sum_b \mathbf 1_{t=\operatorname{owner}(b)} D_b.
--   $$
--
--   Thus each copy retains exactly its owned useful blocks as an actual tensor image; no block-counting surrogate and no duplication of the shared $X$ or $Y$ modes is used.
--
--   **Formalization Note** The theorem is polymorphic in the labelled standard-data bundle, so it applies directly to the literal fifteen-factor Kronecker representation without reducing opaque canonical basis aliases.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and the final zeroing/identification step of the Hole Lemma (Claims 5.8--5.10), PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_owner_projection_standard_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_labelled_broken_owner_projection_realizes_exact_sum
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) {s : ℕ}
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (owner : DWZStandardBlock m → Fin s) (t : Fin s) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    ∀ (shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i),
      (PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
          ∑ block : DWZStandardBlock m,
            if move.symm block ∈ copy.nonholes then
              dwzLabelledUsefulBlockTensor K m D block
            else 0) →
      (∀ block : DWZStandardBlock m, t = owner block →
        move.symm block ∈ copy.nonholes) →
      ∃ f : ∀ i,
          (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
        f 0 = shuffleMap 0 ∧
        f 1 = shuffleMap 1 ∧
        PiTensorProduct.map f (G.blockSubtensor (fun _ ↦ 0)).t =
          ∑ block : DWZStandardBlock m,
            if t = owner block then
              dwzLabelledUsefulBlockTensor K m D block
            else 0 := by
  sorry
