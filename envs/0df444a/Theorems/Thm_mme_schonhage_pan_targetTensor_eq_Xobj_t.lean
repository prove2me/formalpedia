-- Prove2me | Theorems.Thm_mme_schonhage_pan_targetTensor_eq_Xobj_t
-- name    : mme_schonhage_pan_targetTensor_eq_Xobj_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:06:23.292336+00:00
-- url     : https://prove2.me/theorems/d8df2f4a-2ce7-41d7-a881-2b8fd97db3cb
-- title:
--   The Pan target is the triple matrix-multiplication tensor
-- statement:
--   For every field $K$, the explicit target tensor assembled from Pan's three families of pure tensors is exactly the tensor of the direct sum $\langle 1,5,22\rangle \oplus \langle 11,2,5\rangle \oplus \langle 10,11,1\rangle$. This identifies the leading coefficient's coordinate formula with the matrix-multiplication tensor required by the degeneration certificate.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_targetTensor_eq_Xobj_t
    {K : Type u} [Field K] :
    PanLeanBridge.targetTensor (K := K) =
      (PanLeanBridge.Xobj (K := K)).t := by sorry
