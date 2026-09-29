-- Prove2me | Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card
-- name    : mme_ZMod_prime_linear_hash_affine_graph_finset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:33:37.999742+00:00
-- url     : https://prove2.me/theorems/7e778595-e48b-42d9-9d3b-5de0b7107beb
-- title:
--   A uniquely completed affine hash preimage has cardinality $|S|p^n$
-- statement:
--   Let $p$ be prime and let a nonzero linear hash on $n+1$ weight coordinates be restricted to a residue set $S$. Adjoin one affine-offset coordinate, required to equal an arbitrary fixed function of the weight vector. The resulting set of parameter pairs has cardinality $|S|p^n$.
--
--   The theorem packages the exact target-survival count for affine Coppersmith--Winograd hashing: the linear label restriction costs one factor of $p$, while the uniquely determined offset costs the additional affine parameter but does not change the count.
-- source:
--   Elementary finite-field counting; used in the affine-hash target count of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_ZMod_prime_linear_hash_finset_preimage_card

open BigOperators

theorem mme_ZMod_prime_linear_hash_affine_graph_finset_card
    {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (Fin (n + 1) → ZMod p) → ZMod p) :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
      S.card * p ^ n := by
  sorry
