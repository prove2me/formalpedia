-- Prove2me | Theorems.Thm_mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
-- name    : mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:51:26.060073+00:00
-- url     : https://prove2.me/theorems/90899a78-1b11-45f5-ba8b-324e36c97084
-- title:
--   A labelled broken standard tensor includes as the exact sum of its nonhole blocks
-- statement:
--   Let $D$ be a standard trilinear tensor with a distinguished basis of its $Z$-mode, and let every $Z$-basis word carry a finite useful-block label. For a broken copy, write $S$ for its set of nonhole labels and let $D_S$ be the subtensor obtained by retaining exactly the $Z$-basis words labelled by elements of $S$, while leaving the $X$- and $Y$-modes unchanged. If $D_z$ denotes the singleton-label projection of $D$ at $z$, then the canonical modewise inclusions $\iota_i$ satisfy
--
--   $$
--   (\iota_0 \otimes \iota_1 \otimes \iota_2)(D_S)=\sum_{z\in S}D_z.
--   $$
--
--   Thus the literal inclusion of a broken standard tensor is the exact sum of its nonhole useful-block tensors. This is the algebraic decomposition used when the Hole Lemma transports every broken copy into one common standard tensor.
--
--   **Formalization Note** The statement is parametrized by an opaque labelled-data bundle, so concrete DWZ Kronecker bases need not be unfolded during specialization.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the broken standard tensor and its decomposition into available/nonhole blocks in the proof of Claim 5.9; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open BigOperators Finset
open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
    (K : Type u) [Field K] (m : ℕ)
    (D : MME.DWZComponentRestriction.DWZStandardLabelledData K m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZComponentRestriction.DWZStandardBlock m)) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      ∑ block ∈ copy.nonholes,
        MME.DWZComponentRestriction.dwzLabelledUsefulBlockTensor
          K m D block := by
  sorry
