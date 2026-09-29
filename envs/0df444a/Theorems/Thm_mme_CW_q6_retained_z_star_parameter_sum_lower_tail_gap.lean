-- Prove2me | Theorems.Thm_mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap
-- name    : mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:02:00.303174+00:00
-- url     : https://prove2.me/theorems/c6ecb691-12b2-4517-b846-98fea1b9ce22
-- title:
--   Pre-averaging arbitrary-gap lower bound for the total q=6 Z-star incidence
-- statement:
--   Let Z be a finite family of exact q=6 Z-words with uniform address-fiber cardinality B. Under the arbitrary-gap condition MH+R≤B, let K(q) count the shared Z-stars that, at affine parameter q=(w,b₀), have degree at least H and a compatible Z-label in 2S. Then the total star incidence satisfies $$R^2M^{2n+2}|S||Z|\le R^2\sum_q K(q)+2BM^{2n+3}|S||Z|.$$ This pre-averaging form retains the same affine-parameter index needed to combine the Z-star mass with an ordered X/Y collision moment before choosing a bucket.
-- source:
--   CW90 q=6 affine hashing: arbitrary-gap fixed-Z concentration and pre-averaging incidence double counting

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap
    {M n L G B H R : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (Z : Finset (Fin (2 * (n + 1)) → Fin 3))
    (A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (hz : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z)
    (hcard : ∀ z ∈ Z, (A z).card = B)
    (hgap : M * H + R ≤ B)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let degree :
        (Fin (2 * (n + 1)) → Fin 3) →
          (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
      ((A z).attach.filter (fun e =>
        ∑ i,
          ((2 * ((e.1.1 0 i).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
    R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card ≤
      R ^ 2 *
          (∑ q : ((Fin (2 * n + 2) → ZMod M) × ZMod M),
            (Z.filter (fun z =>
              H ≤ degree z q.1 ∧
                ∃ s ∈ S,
                  cwQ6DoubledZHash q.2 q.1 z =
                    2 * (s : ZMod M))).card) +
        2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
  sorry
