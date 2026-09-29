-- Prove2me | Theorems.Thm_mme_six_symmetric_tau_value_to_direct_of_iso
-- name    : mme_six_symmetric_tau_value_to_direct_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:37:46.329796+00:00
-- url     : https://prove2.me/theorems/9b11a44e-3769-483b-88b5-c5a8cddd76a2
-- title:
--   Definition 3.3: six-symmetrized value to direct value under an isomorphism
-- statement:
--   If a tensor's six-symmetrization is isomorphic to its sixth
--   Kronecker power, use monotonicity under restriction and the existing power-root
--   theorem to turn a six-symmetrized witness into a direct witness of the same
--   base. This generic bridge has a short proof once the isomorphism is supplied.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Definition 3.3 (printed p. 18).

import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
open MME
universe u

theorem mme_six_symmetric_tau_value_to_direct_of_iso
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (hV : 0 ≤ V)
    (hsym : TensorObj.Isomorphic
      (sixSymmetrization T) (T.kronPow 6))
    (h : HasSixSymmetricTauValueAtLeast T tau V) :
    HasTauValueAtLeast T tau V := by sorry
