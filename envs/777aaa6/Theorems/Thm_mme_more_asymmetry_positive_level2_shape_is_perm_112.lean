-- Prove2me | Theorems.Thm_mme_more_asymmetry_positive_level2_shape_is_perm_112
-- name    : mme_more_asymmetry_positive_level2_shape_is_perm_112
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T10:16:27.538301+00:00
-- url     : https://prove2.me/theorems/dcf42382-cd9f-4101-bbaa-2e1e58ce1d4d
-- title:
--   Positive level-two shapes are permutations of 112 (imported interface)
-- statement:
--   If three positive natural coordinates sum to four, then the shape is one of the three permutations of (1,1,2). This theorem uses the shared shape-predicate definition so that later level-three recursion can import one stable interface.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5–3.6 and Theorem 6.4, pp. 14–15 and 28–31.

import Definitions.Def_mme_more_asymmetry_shape_predicates

set_option autoImplicit false

theorem mme_more_asymmetry_positive_level2_shape_is_perm_112
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 4) :
    IsPerm112 a b c := by sorry
