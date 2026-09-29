-- Prove2me | Theorems.Thm_integralClosure_exists_complex_ringEquiv_apply_eq
-- name    : integralClosure.exists_complex_ringEquiv_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/306dc415-d1cd-5cd4-a1a4-055d2b738165
-- title:
--   Two maps from the algebraic integers differ by a ℂ-automorphism
-- statement:
--   Let $k$ be a field and let $\varphi, \psi$ be (unital) ring homomorphisms from `integralClosure ℤ ℂ`, the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ — that is, the ring $\bar{\mathbb{Z}}$ of all algebraic integers in $\mathbb{C}$ — to $k$. The assertion is that there exists a ring automorphism $\sigma$ of $\mathbb{C}$ (an isomorphism $\mathbb{C} \simeq \mathbb{C}$ of rings, with no continuity or $\mathbb{R}$-linearity required) such that for all $x, y \in \bar{\mathbb{Z}}$ whose images in $\mathbb{C}$ satisfy $y = \sigma(x)$, one has $\varphi(x) = \psi(y)$ in $k$. Since any ring automorphism of $\mathbb{C}$ carries algebraic integers to algebraic integers, this pairwise formulation is a way of saying $\varphi = \psi \circ \sigma$ on $\bar{\mathbb{Z}}$ without having to name the restriction of $\sigma$ to $\bar{\mathbb{Z}}$. No hypothesis is imposed on $k$ beyond being a field: in particular its characteristic is unconstrained, it is not assumed algebraically closed or algebraic over its prime field, and $\varphi, \psi$ are not assumed injective or surjective.
--
--   This is the statement that the ring of all algebraic integers has, up to the action of the automorphism group of $\mathbb{C}$, only one homomorphism into a given field; classically it rests on the conjugacy under $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ of the primes of $\bar{\mathbb{Z}}$ above a fixed rational prime together with the surjectivity of a decomposition group onto the automorphisms of the residue field. It is used to transport mod $p$ reductions and level structures between different choices of embedding, in the level-raising argument for normalised eigenforms and in the comparison of level automorphisms on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integralClosure_exists_complex_ringEquiv_apply_eq.lean

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y := by sorry
