-- Prove2me | Theorems.Thm_mme_CW_q6_many_retained_z_stars_from_fixed_fiber_lower_tail_gap
-- name    : mme_CW_q6_many_retained_z_stars_from_fixed_fiber_lower_tail_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:54:04.638998+00:00
-- url     : https://prove2.me/theorems/ccf78a2b-eb9e-4a89-ae26-2749236b8119
-- title:
--   Arbitrary-gap fixed-fiber concentration yields one common q=6 parameter with many Z-stars
-- statement:
--   Let Z be a finite family of exact q=6 Z-words, each with an address fiber of the same cardinality B. Hash the X-minus-Z differences over Z/MZ and assume MH+R≤B. For a compatible label set S⊆{0,…,M−1}, there is one common affine parameter (w,b₀) for which the number K(w,b₀) of Z-stars simultaneously having degree at least H and Z-label in 2S satisfies $$R^2|S||Z|\le R^2M K(w,b_0)+2BM|S||Z|.$$ The inequality preserves shared-Z multiplicity and the full arbitrary-gap concentration margin; it makes no X/Y-isolation or tensor-realization claim.
-- source:
--   CW90 q=6 affine hashing: arbitrary-gap fixed-Z concentration, exact offset multiplicity, and incidence averaging

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_many_retained_z_stars_from_fixed_fiber_lower_tail_gap
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
    ∃ w : Fin (2 * n + 2) → ZMod M,
      ∃ b0 : ZMod M,
        R ^ 2 * S.card * Z.card ≤
          R ^ 2 * M *
              (Z.filter (fun z =>
                H ≤ degree z w ∧
                  ∃ s ∈ S,
                    cwQ6DoubledZHash b0 w z =
                      2 * (s : ZMod M))).card +
            2 * B * M * S.card * Z.card := by
  sorry
