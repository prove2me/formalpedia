-- Prove2me | Theorems.Thm_mme_CW_q6_shared_xy_pair_hash_parameter_card
-- name    : mme_CW_q6_shared_xy_pair_hash_parameter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:04:50.120462+00:00
-- url     : https://prove2.me/theorems/69887462-6117-4dfc-be5c-e887c383e75a
-- title:
--   Exact affine-parameter count for one q=6 X/Y collision pair
-- statement:
--   Let e and f be two distinct exact coupled q=6 addresses at power 2(n+1), sharing either their X-word or their Y-word. Over Z/MZ, assume 2 is a unit, and let S be a set of distinct natural representatives modulo M. Then exactly $$|S|M^{2n}$$ affine parameters (w,b_0) simultaneously annihilate the two X-minus-Z difference forms and place the doubled Z-hash of e on a retained label 2S. This is the exact per-pair collision probability |S|/M^3 used in the q=6 first-hash collision sum.
-- source:
--   CW90 q=6 affine-hash collision count for one distinct pair sharing an X- or Y-word

import Mathlib
import Theorems.Thm_mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_shared_xy_pair_hash_parameter_card
    {M n L G : ℕ} [NeZero M]
    (h2 : IsUnit (2 : ZMod M))
    (e f : CWQ6ExactCoupledAddress (n + 1) L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let c : CWQ6ExactCoupledAddress (n + 1) L G →
        Fin (2 * n + 2) → ZMod M := fun a j =>
      (2 * ((a.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
    (((Finset.univ : Finset
        ((Fin (2 * n + 2) → ZMod M) × ZMod M)).filter (fun ω =>
      (∑ i, c e i * ω.1 i = 0) ∧
      (∑ i, c f i * ω.1 i = 0) ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash ω.2 ω.1 (e.1 2) =
          2 * (s : ZMod M))).card) = S.card * M ^ (2 * n) := by
  sorry
