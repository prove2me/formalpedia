-- Prove2me | Theorems.Thm_orderOf_unitOfCoprime_pow_sub_one
-- name    : orderOf_unitOfCoprime_pow_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/c8768799-98d3-5ed2-9be0-ce2e59cd6e3f
-- title:
--   Order of Q modulo Qⁿ-1 equals n
-- statement:
--   Let $Q$ and $n$ be natural numbers with $1 < Q$ and $0 < n$, and suppose $Q$ is coprime to $Q^n - 1$ (the subtraction being truncated subtraction of naturals, harmless here since $Q^n \ge 1$). The coprimality hypothesis $h$ makes the residue of $Q$ a unit of the ring $\mathbb{Z}/(Q^n-1)\mathbb{Z}$, namely `ZMod.unitOfCoprime Q h` in $(\mathbb{Z}/(Q^n-1)\mathbb{Z})^\times$, whose underlying element is the image of $Q$. The assertion is that the order of this unit in the group $(\mathbb{Z}/(Q^n-1)\mathbb{Z})^\times$ is exactly $n$: one has $Q^n \equiv 1 \pmod{Q^n-1}$, and no smaller positive exponent works. Note that the coprimality is taken as a hypothesis rather than derived, even though it holds automatically for $Q>1$ and $n>0$; it is needed to form the unit at all.
--
--   This is the elementary computation underlying the fact that $Q$ generates a cyclic subgroup of order exactly $n$ modulo $Q^n-1$, equivalently that $n$ is the multiplicative order of $Q$ modulo $Q^n-1$. It serves as the arithmetic input for the degree of the unramified cyclotomic layers obtained by adjoining $(q^N-1)$-st roots of unity to a $p$-adic field, and is used in the computation of the relevant field degree and in the construction of cocycles with prescribed local behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_orderOf_unitOfCoprime_pow_sub_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem orderOf_unitOfCoprime_pow_sub_one (Q n : ℕ) (hQ : 1 < Q) (hn : 0 < n)
    (h : Q.Coprime (Q ^ n - 1)) : orderOf (ZMod.unitOfCoprime Q h) = n := by sorry
