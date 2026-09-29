-- Prove2me | Theorems.Thm_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
-- name    : WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/dfecabff-2af2-5233-a222-2322f57ced83
-- title:
--   Carry estimate for Witt addition with slope p-1
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring, $I \subseteq R$ an ideal and $c$ a natural number. Let $x, y \in \mathbb{W}(R)$ be $p$-typical Witt vectors over $R$ (Mathlib's `WittVector p R`) such that every coefficient of $x$ lies in $I$, i.e. $x_i \in I$ for all $i \in \mathbb{N}$, and every coefficient of $y$ satisfies the stronger, $i$-dependent condition $y_i \in I^{p^i + c}$. Then for every $n \in \mathbb{N}$ the $n$-th coefficient of the Witt sum differs from that of $x$ by an element of a high power of $I$: $$(x+y)_n - x_n \in I^{(p-1)n + 1 + c},$$ the exponent being computed in $\mathbb{N}$ (truncated subtraction $p-1$, harmless since $p \ge 2$). Thus a perturbation of $x$ whose $i$-th component lies in $I^{p^i+c}$ moves the $n$-th component of $x$ only within $I^{(p-1)n+1+c}$; the gain over the trivial bound $I^{1+c}$ grows linearly in $n$ with slope $p-1$.
--
--   This is a quantitative continuity statement for addition of Witt vectors with respect to the $I$-adic filtration, of the kind used in the Fontaine-style study of $p$-divisible groups and formal groups over $p$-adic rings. It rests on the weighted homogeneity of the Witt structure polynomials ([`WittVector.isWeightedHomogeneous_wittStructureInt`](thm.html#WittVector.isWeightedHomogeneous_wittStructureInt), applied to the addition polynomials, which are isobaric of weight $p^n$ for the weights $\mathrm{wt}(x_i)=\mathrm{wt}(y_i)=p^i$), and it is used in the formal-group development, for [`MvFormalGroup.coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le`](thm.html#MvFormalGroup.coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
    (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] (I : Ideal R) (c : ℕ)
    (x y : WittVector p R) (hx : ∀ i : ℕ, x.coeff i ∈ I) (hy : ∀ i : ℕ, y.coeff i ∈ I ^ (p ^ i + c))
    (n : ℕ) :
    (x + y).coeff n - x.coeff n ∈ I ^ ((p - 1) * n + 1 + c) := by sorry
