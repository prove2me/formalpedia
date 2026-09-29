-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
-- name    : mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:37:42.380073+00:00
-- url     : https://prove2.me/theorems/9bdec4a6-717c-4d75-b962-66617d0861e3
-- title:
--   Arbitrary-gap lower-tail bound for one q=6 Z-fiber
-- statement:
--   Fix one exact q=6 Z-fiber of cardinality B and hash its addresses by their X-minus-Z difference forms over Z/MZ. Assume the standard unit hypotheses. If a threshold H and gap R satisfy MH+R≤B, then the number of weights whose surviving fiber degree is below H satisfies $$R^2\,|\{w:D_z(w)<H\}|\le 2BM^{2n+3}.$$ This arbitrary-gap form permits thresholds close to the mean B/M and is the concentration estimate needed to couple many retained Z-stars to the X/Y collision budget.
-- source:
--   CW90 q=6 fixed-fiber affine hashing; arbitrary-gap consequence of the exact first and second moments

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment
import Theorems.Thm_mme_finite_variance_lower_tail_gap_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
    {M n L G B H R : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z)
    (hcard : A.card = B)
    (hgap : M * H + R ≤ B) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    R ^ 2 * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
      (fun w => ¬ H ≤ (A.attach.filter
        (fun e => ∑ i, c e i * w i = 0)).card)).card) ≤
      2 * B * M ^ (2 * n + 3) := by
  sorry
