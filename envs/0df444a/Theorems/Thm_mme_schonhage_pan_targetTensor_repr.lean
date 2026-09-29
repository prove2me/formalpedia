-- Prove2me | Theorems.Thm_mme_schonhage_pan_targetTensor_repr
-- name    : mme_schonhage_pan_targetTensor_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:14.481151+00:00
-- url     : https://prove2.me/theorems/57ec938c-9e42-4319-a436-dd11977bdbf4
-- title:
--   Coordinates of the Pan target tensor
-- statement:
--   In the explicit tensor-product basis, every coordinate of Pan's target tensor is the signed sum of the three desired matrix-multiplication coordinate monomials. This is the tensor-side counterpart of the scalar degree-12 calculation.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME BigOperators
universe u

theorem mme_schonhage_pan_targetTensor_repr
    {K : Type u} [Field K]
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        (PanLeanBridge.targetTensor (K := K)) q =
      ∑ s : Fin 2,
        PanLeanBridge.targetSide (K := K) (q 0) (q 1) (q 2) s := by sorry
