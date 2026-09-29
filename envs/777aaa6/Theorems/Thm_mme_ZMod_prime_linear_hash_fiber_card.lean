-- Prove2me | Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card
-- name    : mme_ZMod_prime_linear_hash_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:00:36.548492+00:00
-- url     : https://prove2.me/theorems/2928563d-00ad-427d-a742-0378da518787
-- title:
--   Every fiber of a nonzero prime-field linear hash has size $p^n$
-- statement:
--   Let $p$ be prime and let $c=(c_0,\dots,c_n)$ be a vector over $\mathbb Z/p\mathbb Z$ with at least one nonzero coordinate.  For every residue $s$, the affine hyperplane
--
--   $$
--   \left\{w\in(\mathbb Z/p\mathbb Z)^{n+1}:\sum_i c_iw_i=s\right\}
--   $$
--
--   has exactly $p^n$ elements.  Equivalently, a nonzero linear hash of $n+1$ independent prime-field weights is exactly uniform.  This is the finite counting fact used when an affine Coppersmith--Winograd hash imposes one nontrivial collision equation.
-- source:
--   Elementary finite-field linear algebra; used in the affine-hash collision count of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

theorem mme_ZMod_prime_linear_hash_fiber_card
    {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (s : ZMod p) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod p =>
      ∑ i, c i * w i = s)).card) = p ^ n := by
  sorry
