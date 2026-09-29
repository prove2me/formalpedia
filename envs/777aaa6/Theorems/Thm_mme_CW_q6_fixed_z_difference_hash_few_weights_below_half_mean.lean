-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_few_weights_below_half_mean
-- name    : mme_CW_q6_fixed_z_difference_hash_few_weights_below_half_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:40:02.617361+00:00
-- url     : https://prove2.me/theorems/7cb10941-b9ab-456a-97c7-c2ee909c334a
-- title:
--   A fixed q=6 Z-fiber has few difference-hash weights below half its mean
-- statement:
--   Fix one regular Z-fiber of B exact coupled q=6 addresses and hash it by the CW difference equation over ZMod M. If 2 is a unit modulo M, G is positive, and H is at most half the mean fiber degree B/M, then the number of weight vectors for which the surviving degree is below H is at most 8 M^(2n+3)/B. Equivalently, B times that bad-weight count is at most 8 M times the total number M^(2n+2) of weight vectors. This is a sharp lower-tail consequence of the exact first and second moments and preserves the shared Z-fiber structure.
-- source:
--   CW90 q=6 first-hash lower-tail estimate from exact fixed-fiber moments

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment
import Theorems.Thm_mme_finite_variance_below_half_mean_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_fixed_z_difference_hash_few_weights_below_half_mean
    {M n L G B H : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z)
    (hcard : A.card = B) (hB : 0 < B)
    (hH : 2 * M * H ≤ B) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    B * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
      (fun w => ¬ H ≤ (A.attach.filter
        (fun e => ∑ i, c e i * w i = 0)).card)).card) ≤
      8 * M * M ^ (2 * n + 2) := by
  sorry
