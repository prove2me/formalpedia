-- Prove2me | Theorems.Thm_eq_one_of_isNilpotent_sub_one_of_pow_eq_one
-- name    : eq_one_of_isNilpotent_sub_one_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/8208ffd0-abcb-5bf4-bc7c-3162674843d2
-- title:
--   Unipotent element of order a unit is trivial
-- statement:
--   Let $A$ be a ring, not assumed commutative, and let $u \in A$ be an element such that $u - 1$ is nilpotent, i.e. $(u-1)^k = 0$ for some $k$. Let $m$ be a natural number whose image $m \cdot 1_A$ under the canonical map $\mathbb{N} \to A$ is a unit of $A$. Assume $u^m = 1$. Then $u = 1$. No hypothesis of positivity on $m$ is imposed beyond the invertibility of its image (which in particular excludes $m = 0$ unless $A$ is trivial), and no finiteness or commutativity assumption is placed on $A$.
--
--   This is the elementary statement that a unipotent element of a ring has no torsion of order invertible in the ring — classically, that a unipotent matrix of finite order prime to the characteristic is the identity. It is used in the proof of [`Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast`](thm.html#Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_eq_one_of_isNilpotent_sub_one_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem eq_one_of_isNilpotent_sub_one_of_pow_eq_one
    {A : Type*} [Ring A] {u : A} (hu : IsNilpotent (u - 1))
    {m : ℕ} (hm : IsUnit (m : A)) (h : u ^ m = 1) :
    u = 1 := by sorry
