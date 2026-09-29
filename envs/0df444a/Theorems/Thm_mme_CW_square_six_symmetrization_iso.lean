-- Prove2me | Theorems.Thm_mme_CW_square_six_symmetrization_iso
-- name    : mme_CW_square_six_symmetrization_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:40:21.439461+00:00
-- url     : https://prove2.me/theorems/174e242f-7fd0-47c3-a355-3c0cf7347f21
-- title:
--   DWZ Definition 3.3: the symmetric CW square collapses to its sixth power
-- statement:
--   Rename the modes in all six factors of the full symmetrization of
--   the symmetric Coppersmith--Winograd tensor square, obtaining an isomorphism to
--   six ordinary copies of that square. This is the only CW-specific tensor leaf
--   between the source-faithful Equation (25) value and a direct tau-value witness.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Definition 3.3 (printed p. 18) and the symmetric CW tensor of Section 3.4.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_CW_tensor
open MME
universe u

theorem mme_CW_square_six_symmetrization_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization
        (TensorObj.kron (CWObj K q) (CWObj K q)))
      ((TensorObj.kron (CWObj K q) (CWObj K q)).kronPow 6) := by sorry
