-- Prove2me | Theorems.Thm_mme_ZMod_prime_linear_hash_finset_preimage_card
-- name    : mme_ZMod_prime_linear_hash_finset_preimage_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:05:22.773738+00:00
-- url     : https://prove2.me/theorems/56e26107-f650-444d-8fe3-a6b2f5569e9e
-- title:
--   A nonzero prime-field linear hash pulls back $S$ to $|S|p^n$ points
-- statement:
--   Let $p$ be prime and let $L:(\mathbb Z/p\mathbb Z)^{n+1}\to\mathbb Z/p\mathbb Z$ be a nonzero linear hash.  For every finite residue set $S$,
--
--   $$
--   |L^{-1}(S)|=|S|p^n.
--   $$
--
--   Thus restricting a uniformly distributed nonzero linear hash to a progression-free set retains exactly the expected $|S|/p$ fraction of all weight vectors.
-- source:
--   Elementary finite-field linear algebra; used in the affine-hash target count of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card

open BigOperators

theorem mme_ZMod_prime_linear_hash_finset_preimage_card
    {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p)) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod p =>
      (∑ i, c i * w i) ∈ S)).card) = S.card * p ^ n := by
  sorry
