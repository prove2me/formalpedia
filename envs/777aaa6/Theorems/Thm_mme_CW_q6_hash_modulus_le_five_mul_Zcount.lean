-- Prove2me | Theorems.Thm_mme_CW_q6_hash_modulus_le_five_mul_Zcount
-- name    : mme_CW_q6_hash_modulus_le_five_mul_Zcount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:18:41.477275+00:00
-- url     : https://prove2.me/theorems/2ea47371-98cc-4eba-b4d3-aea3e447b09a
-- title:
--   The q=6 hash modulus is at most five times the third-word count
-- statement:
--   Let $L+G=N$, and put
--
--   $$
--   X=\binom NG,\qquad Z=\binom{2N}{L}\binom{2N-L}{L},\qquad M=4X^2+1.
--   $$
--
--   Then $M\le5Z$. Thus a three-progression-free set with at least eighty elements automatically makes the integer hash-family quotient $|S|Z/(16M)$ nonzero. The estimate is uniform, including profiles where $L$ is small.
-- source:
--   Elementary binomial comparison for the q=6 Coppersmith--Winograd affine-hash modulus and exact third-word count.

import Mathlib

theorem mme_CW_q6_hash_modulus_le_five_mul_Zcount
    {N L G : ℕ} (hsum : L + G = N) :
    4 * (Nat.choose N G) ^ 2 + 1 ≤
      5 * (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) := by
  sorry
