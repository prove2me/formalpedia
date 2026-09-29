-- Prove2me | solution 1 for mme_more_asymmetry_positive_level2_shape_is_perm_112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T10:19:17.237472+00:00
-- url     : https://prove2.me/submissions/7d894b0f-38c3-429c-a622-a26bca6cd278

import Definitions.Def_mme_more_asymmetry_shape_predicates

set_option autoImplicit false

theorem solution
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 4) :
    IsPerm112 a b c := by
  simp only [IsPerm112]
  omega
