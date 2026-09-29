-- Prove2me | Theorems.Thm_mme_ZMod_unit_linear_hash_finset_preimage_card
-- name    : mme_ZMod_unit_linear_hash_finset_preimage_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:20:25.773969+00:00
-- url     : https://prove2.me/theorems/1b9817dc-c1bd-45e7-9e32-5eb73c721674
-- title:
--   A unit-coefficient modular hash pulls back $S$ to $|S|M^n$ points
-- statement:
--   Let $M>0$ and let $L:(\mathbb Z/M\mathbb Z)^{n+1}\to\mathbb Z/M\mathbb Z$ be a linear hash having at least one unit coefficient. For every residue set $S$,
--
--   $$
--   |L^{-1}(S)|=|S|M^n.
--   $$
--
--   Thus restricting such a hash to a progression-free residue set retains exactly the expected $|S|/M$ fraction of all weight vectors, even when $M$ is composite.
-- source:
--   Elementary finite abelian-group counting; used in the affine-hash analysis of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card

open BigOperators

theorem mme_ZMod_unit_linear_hash_finset_preimage_card
    {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j)) (S : Finset (ZMod M)) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod M =>
      (∑ i, c i * w i) ∈ S)).card) = S.card * M ^ n := by
  sorry
