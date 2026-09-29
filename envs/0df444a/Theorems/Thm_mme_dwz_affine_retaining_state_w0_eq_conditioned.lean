-- Prove2me | Theorems.Thm_mme_dwz_affine_retaining_state_w0_eq_conditioned
-- name    : mme_dwz_affine_retaining_state_w0_eq_conditioned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T00:15:58.870377+00:00
-- url     : https://prove2.me/theorems/544770c5-2228-417d-8966-bf56cccfb0db
-- title:
--   A retained affine state's label is its conditioned hash value
-- statement:
--   For a Table-2 affine state retaining a supported address triple I, J, K with I+J+K=4 coordinatewise, the state label q.2 equals the conditioned X--Z hash value: twice the I-weighted sum minus the (4-K)-weighted sum. This identifies the common canonical first-hash state with the second-hash parameter used in Claim 6.8.
-- source:
--   Duan--Wu--Zhou, asymmetric hashing definitions and Claim 6.8, pp. 50--52.

import Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_weight_label

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_affine_retaining_state_w0_eq_conditioned
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = (4 : ZMod p))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (hretains : MME.dwzAsymmetricAffineRetains
      (4 : ZMod p) S I J K q) :
    q.2 =
      2 * (∑ t : Fin (N + 1), I t * q.1 t.castSucc) -
        ∑ t : Fin (N + 1),
          ((4 : ZMod p) - K t) * q.1 t.castSucc := by
  sorry
