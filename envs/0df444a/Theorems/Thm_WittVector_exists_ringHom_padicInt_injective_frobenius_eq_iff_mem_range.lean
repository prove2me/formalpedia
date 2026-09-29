-- Prove2me | Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
-- name    : WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/8377537d-54d8-5c4a-97f4-8573c8e3a724
-- title:
--   Frobenius-fixed Witt vectors form a copy of ℤₚ
-- statement:
--   Let $p$ be a prime and let $K$ be a field of characteristic $p$ (a type in the lowest universe). The assertion is the existence of a ring homomorphism $c \colon \mathbb{Z}_p \to \mathbb{W}(K)$ from the $p$-adic integers to the ring of $p$-typical Witt vectors over $K$, such that two conditions hold: first, $c$ is injective as a function; second, for every Witt vector $w \in \mathbb{W}(K)$ one has $\mathrm{frobenius}(w) = w$ if and only if $w$ lies in the set-theoretic range of $c$. Here $\mathrm{frobenius}$ is the Witt-vector Frobenius endomorphism of `WittVector p K`, which in characteristic $p$ acts on coefficients by $x \mapsto x^p$. Thus the subring of Frobenius-fixed elements of $\mathbb{W}(K)$ is, as a set, exactly the image of an embedded copy of $\mathbb{Z}_p$. The homomorphism $c$ is merely asserted to exist, not specified by the statement; the witness used is the composition of the Mathlib isomorphism $\mathbb{Z}_p \cong \mathbb{W}(\mathbb{F}_p)$ with the map $\mathbb{W}(\mathbb{F}_p) \to \mathbb{W}(K)$ functorially induced by the inclusion of the prime field.
--
--   This identifies the Frobenius-invariants of $\mathbb{W}(K)$, for $K$ of characteristic $p$, with a copy of $\mathbb{Z}_p$ — the standard statement that $\mathbb{W}(\mathbb{F}_p) = \mathbb{Z}_p$ sits inside $\mathbb{W}(K)$ as the fixed ring of $\sigma$. It is used in the Čerednik–Drinfel'd part of the development, where invariants of formal $\mathcal{O}_D$-modules under a Frobenius-type operator are turned into $\mathbb{Z}_p$-modules of prescribed rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    ∃ c : ℤ_[p] →+* WittVector p K, Function.Injective c ∧
      ∀ w : WittVector p K, WittVector.frobenius w = w ↔ w ∈ Set.range c := by sorry
