-- Prove2me | Theorems.Thm_mme_CW_q6_exact_subtype_collision_universe_card_le
-- name    : mme_CW_q6_exact_subtype_collision_universe_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:20:32.922321+00:00
-- url     : https://prove2.me/theorems/bb7e376a-cc42-42e0-8fc5-98e2b7ca0f81
-- title:
--   Exact q=6 regularity bounds the ordered X/Y collision universe
-- statement:
--   Assume the exact coupled q=6 profile at parameters N,L,G has the CW regularity counts. Let E be its finite exact-address subtype and let C be the ordered set of distinct pairs sharing their X-word or their Y-word. Then $$|C|\le 2\left(\binom{2N}{L}\binom{2N-L}{L}\binom{2G}{G}\right)\binom NG^2.$$ This is the deterministic collision-universe bound used before applying the exact per-pair affine-hash probability.
-- source:
--   CW90 q=6 exact-profile biregularity and ordered X/Y collision double counting

import Mathlib
import Theorems.Thm_mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
import Definitions.Def_mme_CW_q6_exact_address_incidence

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6CollisionUniverseExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

noncomputable local instance q6CollisionUniverseCoupledAddressFintype
    (N : ℕ) : Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

noncomputable local instance q6CollisionUniverseExactAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  Fintype.ofInjective (fun e => e.1) Subtype.val_injective

theorem mme_CW_q6_exact_subtype_collision_universe_card_le
    (N L G : ℕ)
    (hregular : CWQ6ExactAddressRegularity N L G) :
    let E : Finset (CWQ6ExactCoupledAddress N L G) := Finset.univ
    ((E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧
        (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card ≤
      2 *
        ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G) *
        (Nat.choose N G) ^ 2 := by
  sorry
