-- Prove2me | Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card
-- name    : mme_ZMod_unit_linear_hash_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:14:16.158795+00:00
-- url     : https://prove2.me/theorems/0ab4b1ea-1ace-41be-80cf-83346ec785e4
-- title:
--   A linear hash with a unit coefficient has exactly $M^n$ points in every fiber
-- statement:
--   Let $M>0$ and let $c=(c_0,\dots,c_n)$ be a vector over the residue ring $\mathbb Z/M\mathbb Z$. If one coefficient $c_j$ is a unit, then for every residue $s$ the affine fiber
--
--   $$
--   \left\{w\in(\mathbb Z/M\mathbb Z)^{n+1}:\sum_i c_iw_i=s\right\}
--   $$
--
--   has exactly $M^n$ elements. Thus a linear modular hash remains exactly uniform for composite moduli whenever one variable has an invertible coefficient. This is the form required by the $q=6$ Coppersmith--Winograd hash, whose odd modulus is not assumed prime.
-- source:
--   Elementary finite abelian-group counting; used in the affine-hash analysis of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

theorem mme_ZMod_unit_linear_hash_fiber_card
    {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j)) (s : ZMod M) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod M =>
      ∑ i, c i * w i = s)).card) = M ^ n := by
  sorry
