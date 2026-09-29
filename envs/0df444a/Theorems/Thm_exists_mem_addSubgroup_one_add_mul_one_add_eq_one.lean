-- Prove2me | Theorems.Thm_exists_mem_addSubgroup_one_add_mul_one_add_eq_one
-- name    : exists_mem_addSubgroup_one_add_mul_one_add_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/9d8abe80-b18a-5da2-80ed-9a2a77cb5fa3
-- title:
--   1+M consists of units when M is closed, multiplicative and of norm <1
-- statement:
--   Let $L$ be a complete normed field and let $M$ be an additive subgroup of $L$ satisfying three conditions: the underlying set of $M$ is closed in $L$; $M$ is closed under multiplication, i.e. $xy \in M$ whenever $x, y \in M$; and every element of $M$ has norm strictly less than $1$. Then for every $x \in M$ there exists $y \in M$ with $(1+x)(1+y) = 1$. Thus each element of the coset $1 + M$ is invertible in $L$ with inverse again lying in $1 + M$; in particular $1 + M$ is a subgroup of $L^{\times}$, although the Lean statement records only the existence of the inverse inside $1 + M$ for a given $x$.
--
--   This is the standard statement that a closed, multiplicatively closed additive subgroup of a complete normed field consisting of elements of norm $< 1$ gives rise to the multiplicative group $1 + M$ (the typical case being a maximal ideal of the ring of integers of a local field). It is used in the construction of subgroups of units on which prescribed maps are multiplicative cocycles, at [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_mem_addSubgroup_one_add_mul_one_add_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_mem_addSubgroup_one_add_mul_one_add_eq_one
    {L : Type*} [NormedField L] [CompleteSpace L]
    (M : AddSubgroup L) (hMclosed : IsClosed (M : Set L)) (hMmul : ∀ x y : L, x ∈ M → y ∈ M → x * y ∈ M)
    (hMnorm : ∀ x ∈ M, ‖x‖ < 1) {x : L} (hx : x ∈ M) :
    ∃ y ∈ M, (1 + x) * (1 + y) = 1 := by sorry
