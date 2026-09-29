-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_weight_label
-- name    : mme_dwz_asymmetric_affine_retains_iff_weight_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:32:33.365307+00:00
-- url     : https://prove2.me/theorems/aa416111-0b15-4a47-8692-fecccce684a6
-- title:
--   Normal form for a DWZ affine state retaining one supported word
-- statement:
--   Let an odd-prime DWZ affine hash state retain a coordinatewise supported triple of words I,J,K. Retention is equivalent to two explicit conditions: the affine X-hash label lies in S, and the state scalar w0 equals the difference of the weighted I- and J-sums. Thus, after the weight word is fixed, choosing a common label determines the remaining affine coordinates uniquely.
-- source:
--   Duan--Wu--Zhou asymmetric affine hashing; normal form underlying the singleton incidence count and Claim 6.8 averaging.

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity

open BigOperators
open MME

set_option autoImplicit false

theorem mme_dwz_asymmetric_affine_retains_iff_weight_label
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    MME.dwzAsymmetricAffineRetains levelSum S I J K q ↔
      q.1 (Fin.last (N + 1)) +
            ∑ t : Fin (N + 1), I t * q.1 t.castSucc ∈ S ∧
        q.2 =
          (∑ t : Fin (N + 1), I t * q.1 t.castSucc) -
            ∑ t : Fin (N + 1), J t * q.1 t.castSucc := by
  sorry
