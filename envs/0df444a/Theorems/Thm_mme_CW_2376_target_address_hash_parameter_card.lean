-- Prove2me | Theorems.Thm_mme_CW_2376_target_address_hash_parameter_card
-- name    : mme_CW_2376_target_address_hash_parameter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:18:31.50153+00:00
-- url     : https://prove2.me/theorems/28e4735f-7149-4fc0-9ebe-dd8644d8eb5e
-- title:
--   A CW marginal edge survives in exactly $|S|p^N$ augmented hash states
-- statement:
--   Let $a$ be any supported Coppersmith--Winograd address of positive scale whose three mode words have the optimized five-grade marginals. Let $p$ be an odd prime and let $S$ be a set of integer labels below $p/2$. Among the augmented affine hash states, exactly
--
--   $$
--   |S|p^N
--   $$
--
--   states retain $a$, where $N=3{,}000{,}000m$. One nonzero grade-one coefficient makes the first label uniformly distributed, equality of the second hash uniquely determines the affine offset, and the CW three-term identity forces the third hash to the same label. The result applies to every ambient marginal edge, and hence in particular to each exact-profile target edge.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine hashing and Salem--Spencer restriction on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_augmented_hash_states
import Theorems.Thm_mme_CW_2376_modular_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card
import Theorems.Thm_mme_CW_2376_modular_hash_XY_normal_forms
import Theorems.Thm_mme_CW_2376_marginal_address_has_grade_one
import Theorems.Thm_mme_lower_half_ZMod_image_card

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_CW_2376_target_address_hash_parameter_card
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hpodd : Odd p) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (a : CW2376MarginalSupportedAddress m) :
    (cw2376AugmentedHashStatesRetainingAddress m p S a).card =
      S.card * p ^ cw2376ProfileLength m := by
  sorry
