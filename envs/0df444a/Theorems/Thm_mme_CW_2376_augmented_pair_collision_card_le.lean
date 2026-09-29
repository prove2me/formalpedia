-- Prove2me | Theorems.Thm_mme_CW_2376_augmented_pair_collision_card_le
-- name    : mme_CW_2376_augmented_pair_collision_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:15:42.070542+00:00
-- url     : https://prove2.me/theorems/0a7f3981-5136-4724-bdf3-f7f8a97f36f4
-- title:
--   A colliding CW edge pair survives in at most $p^N$ augmented hash states
-- statement:
--   Let $a$ and $b$ be two distinct supported Coppersmith--Winograd addresses with the prescribed five-grade marginals, and suppose they share one mode word. For an odd prime $p$ at least five, the number of augmented affine hash states that retain both addresses is at most $p^N$, where $N=3{,}000{,}000m$.
--
--   Sharing one mode forces the two retained labels to agree. Since two supported addresses are determined by any two modes, a different mode word remains; its hash equality supplies a nonzero linear equation in the weights. Equality of the first two hashes for $a$ uniquely determines the affine offset. These two independent conditions remove two factors of $p$ from the $p^{N+2}$ parameter space.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), collision deletion for affine outer hashes on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_augmented_hash_states
import Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le
import Theorems.Thm_mme_Fin5_word_difference_nonzero_in_ZMod
import Theorems.Thm_mme_CW_2376_supported_two_modes_determine_address
import Theorems.Thm_mme_CW_2376_modular_hash_XY_normal_forms

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_CW_2376_augmented_pair_collision_card_le
    (m p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (a b : CW2376MarginalSupportedAddress m)
    (hab : a ≠ b) (i : Fin 3) (hshare : a.1 i = b.1 i) :
    ((cw2376AugmentedHashStatesRetainingAddress m p S a ∩
      cw2376AugmentedHashStatesRetainingAddress m p S b).card) ≤
        p ^ cw2376ProfileLength m := by
  sorry
