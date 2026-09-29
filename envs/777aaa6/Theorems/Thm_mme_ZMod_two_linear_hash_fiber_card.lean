-- Prove2me | Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card
-- name    : mme_ZMod_two_linear_hash_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:56:49.038746+00:00
-- url     : https://prove2.me/theorems/7f5ef762-7134-4cc0-bcad-e9e3fb0a2f2f
-- title:
--   Exact joint fibers of two linear hashes over a residue ring
-- statement:
--   Let two linear forms on $(\mathbb Z/M\mathbb Z)^{n+2}$ have coefficient rows $c$ and $d$. If some $2\times2$ minor $c_jd_k-c_kd_j$ is a unit modulo $M$, then the forms are jointly uniform: for every target pair $(s,t)$,
--
--   $$
--   \left|\left\{w:\sum_i c_iw_i=s,\ \sum_i d_iw_i=t\right\}\right|=M^n.
--   $$
--
--   The modulus may be composite. This is the exact finite-module counting kernel used to control nondegenerate pairs in affine-hash second-moment arguments.
-- source:
--   Elementary finite-module linear algebra: invert a unit 2-by-2 minor, then count the equal fibers of the resulting surjective additive homomorphism

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_ZMod_two_linear_hash_fiber_card {M n : ℕ} [NeZero M]
    (c d : Fin (n + 2) → ZMod M)
    (j k : Fin (n + 2))
    (hdet : IsUnit (c j * d k - c k * d j))
    (s t : ZMod M) :
    ((Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
      (∑ i, c i * w i = s) ∧ (∑ i, d i * w i = t))).card) = M ^ n := by
  sorry
