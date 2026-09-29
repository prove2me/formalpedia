-- Prove2me | Theorems.Thm_mme_dwz_source_broken_owner_projector_diagonal
-- name    : mme_dwz_source_broken_owner_projector_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:19:35.031073+00:00
-- url     : https://prove2.me/theorems/29f9ed32-82c4-4ce5-8427-5464846dc04a
-- title:
--   Exact full-power projector onto one whole source-aligned broken owner
-- statement:
--   Fix one length-$N$ Table-2 outer word and one literal broken copy over its useful fine-$Z$ words. In each mode, first project the $N$th power of $CW_6\otimes CW_6$ onto the outer word's coarse five-graded address. Then apply the broken copy's secondary all-zero projector, which leaves the complete $X$ and $Y$ spaces and retains exactly its allowed $Z$-basis words. The resulting three mode maps send the full source tensor exactly to the tensor of the whole source-aligned broken-address object.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Claim 6.8 and the ensuing broken-copy zeroing step.

import Theorems.Thm_mme_gradedAddressProj_then_blockProj_preserves_tensor
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_owner_projector_diagonal
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    PiTensorProduct.map
        (fun i ↦
          ((DWZSourceAligned.brokenAddressGrading K m outer copy).blockProj i 0).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (DWZSourceAligned.coarseAddress outer) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
      (DWZSourceAligned.brokenAddressObj K m outer copy).t := by
  sorry
