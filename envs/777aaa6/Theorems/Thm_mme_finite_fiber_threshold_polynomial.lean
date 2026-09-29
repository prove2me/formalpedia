-- Prove2me | Theorems.Thm_mme_finite_fiber_threshold_polynomial
-- name    : mme_finite_fiber_threshold_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:57:34.837032+00:00
-- url     : https://prove2.me/theorems/a07622e1-202a-410a-8cd2-545431c0db61
-- title:
--   Polynomial-loss uniform threshold for finite fibers
-- statement:
--   Let $A$ fibers each have capacity at most $H>0$, and let $t_a\le H$ count the retained objects in fiber $a$. If the total retained mass loses at most a factor $Q>0$, in the sense that
--
--   $$AH\le Q\sum_{a=1}^{A}t_a,$$
--
--   then there are a positive uniform threshold $H'$ and a set $S$ of fibers such that every $a\in S$ contains at least $H'$ retained objects and
--
--   $$A\le2Q|S|,\qquad H\le4QH'.$$
--
--   Consequently the cubic-square capacity $A^3H^2$ is preserved after uniformly truncating the fibers in $S$, up to the polynomial factor $128Q^5$. This is the regularization step used after choosing one common balanced position halving for the paired q=6 hash family.
-- source:
--   Finite averaging and threshold argument used in the common-halving refinement of Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5-6.

import Mathlib.Tactic
import Mathlib.Data.Finset.Card

open BigOperators

set_option autoImplicit false

theorem mme_finite_fiber_threshold_polynomial
    (A H Q : ℕ) (hH : 0 < H) (hQ : 0 < Q)
    (t : Fin A → ℕ) (ht : ∀ a, t a ≤ H)
    (hmass : A * H ≤ Q * ∑ a, t a) :
    ∃ H' : ℕ, ∃ S : Finset (Fin A),
      0 < H' ∧
      (∀ a ∈ S, H' ≤ t a) ∧
      A ≤ 2 * Q * S.card ∧
      H ≤ 4 * Q * H' := by
  sorry
