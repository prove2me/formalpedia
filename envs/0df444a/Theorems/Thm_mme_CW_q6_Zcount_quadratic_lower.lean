-- Prove2me | Theorems.Thm_mme_CW_q6_Zcount_quadratic_lower
-- name    : mme_CW_q6_Zcount_quadratic_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:09:36.3005+00:00
-- url     : https://prove2.me/theorems/02504a53-29ad-4a00-8be3-d532cd05fca1
-- title:
--   The exact q=6 third-word count has a uniform quadratic lower bound
-- statement:
--   Let $L,G>0$ with $L+G=N$. The number
--
--   $$
--   Z=\binom{2N}{L}\binom{2N-L}{L}
--   $$
--
--   of exact third-mode words in the coupled $q=6$ profile satisfies the uniform lower bound $Z\ge 2N^2$. This ensures that the raw family size grows fast enough to absorb the final integer-division loss in the affine-hash extraction, even in the smallest admissible-$L$ regime.
-- source:
--   Elementary binomial estimate for the exact-profile word count in the q=6 Coppersmith--Winograd hashing construction.

import Mathlib.Data.Nat.Choose.Basic

theorem mme_CW_q6_Zcount_quadratic_lower
    {N L G : ℕ} (hL : 0 < L) (hsum : L + G = N) (hG : 0 < G) :
    2 * N * N ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L := by
  sorry
