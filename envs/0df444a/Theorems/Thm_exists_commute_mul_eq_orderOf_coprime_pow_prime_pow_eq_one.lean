-- Prove2me | Theorems.Thm_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
-- name    : exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d27f630d-6617-54ea-9134-2555fc0df6ef
-- title:
--   Decomposition of a group element into p'- and p-parts
-- statement:
--   Let $p$ be a prime and let $G$ be a finite group, written multiplicatively, and let $g \in G$. Then there exist elements $g', u \in G$ such that $g' u = g$; $g'$ and $u$ commute; the order of $g'$ is coprime to $p$; there is a natural number $a$ with $u^{p^a} = 1$; and both $g'$ and $u$ lie in the subgroup $\langle g\rangle$ of integer powers of $g$ (`Subgroup.zpowers g`). Thus every element of a finite group factors as a product of a commuting pair consisting of an element of order prime to $p$ and an element of $p$-power order, both of them powers of the original element. The statement asserts existence only; no uniqueness of the pair $(g', u)$ is claimed, and the exponent $a$ is not tied to the $p$-adic valuation of the order of $g$.
--
--   This is the classical decomposition of an element of a finite group into its $p$-regular ($p'$-) part $g_{p'}$ and its $p$-part $g_p$, the group-theoretic analogue of a Jordan decomposition. It is used in [`Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero`](thm.html#Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero), where trace identities valid on $p$-regular elements in characteristic $p$ are propagated to all elements of the group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (g : G) :
    ∃ g' u : G, g' * u = g ∧ Commute g' u ∧ (orderOf g').Coprime p ∧ (∃ a : ℕ, u ^ p ^ a = 1) ∧
      g' ∈ Subgroup.zpowers g ∧ u ∈ Subgroup.zpowers g := by sorry
