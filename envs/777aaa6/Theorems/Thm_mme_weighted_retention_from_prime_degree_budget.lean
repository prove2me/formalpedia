-- Prove2me | Theorems.Thm_mme_weighted_retention_from_prime_degree_budget
-- name    : mme_weighted_retention_from_prime_degree_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:29:16.174751+00:00
-- url     : https://prove2.me/theorems/928252fb-a5dc-46c7-96b0-a87e17fff298
-- title:
--   A retained-family count preserves a strict weighted surplus
-- statement:
--   Let $C$ be the ambient edge count, $D$ a collision-degree parameter, $P$ a hashing prime, $S$ the number of allowed labels, and $M$ the number of retained induced edges. Suppose
--
--   $$
--   P\leq DF,\qquad 6D\leq S,\qquad C\frac{S}{2P^2}\leq M.
--   $$
--
--   For every nonnegative block value $B$, a strict pre-hashing surplus
--
--   $$
--   VDF^2<CB
--   $$
--
--   then implies the post-hashing weighted bound $V<MB$. This elementary bookkeeping lemma is the final numerical bridge used after Behrend hashing in the $\Phi_{125}$, $\Phi_{134}$, and related laser-method constituents.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the pruning and retained-family estimates in Lemma 3.3, pp. 359--360; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem mme_weighted_retention_from_prime_degree_budget
    (P D F S C M B V : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hF : 0 < F)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hprime : P ≤ D * F)
    (hlabels : 6 * D ≤ S)
    (hkept : C * (S / (2 * P ^ 2)) ≤ M)
    (hbudget : V * D * F ^ 2 < C * B) :
    V < M * B := by
  sorry
