-- Prove2me | Theorems.Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP
-- name    : WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a47e3d54-f70a-5aac-9244-b0932ceaa3ae
-- title:
--   Ring maps from W(𝔽_{p²}) agree up to Frobenius
-- statement:
--   Let $p$ be a prime and let $K$ be a field (in a fixed universe) of characteristic $p$. Write $\mathbb{F}_{p^2}$ for Mathlib's model `GaloisField p 2` of the field with $p^2$ elements, and $W(\mathbb{F}_{p^2})$ for the ring of $p$-typical Witt vectors over it. Let $a$ and $b$ be two ring homomorphisms $W(\mathbb{F}_{p^2}) \to K$. The assertion is the disjunction: either $a = b$, or $a$ equals the composite `b.comp WittVector.frobenius`, that is $a(x) = b(\sigma x)$ for all $x$, where $\sigma$ is the Frobenius ring endomorphism of $W(\mathbb{F}_{p^2})$. No further hypotheses are imposed on $K$ — it is not assumed perfect, finite, or complete — and the two alternatives are not claimed to be exclusive (they coincide exactly when $a$ and $b$ kill the same elements in a way making $\sigma$ act trivially, e.g. when both are the zero-characteristic-incompatible case cannot occur since $K$ is a field of characteristic $p$).
--
--   This is the Witt-vector form of the statement that the two embeddings of the unramified quadratic extension $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ of $\mathbb{Z}_p$ into a ring of characteristic $p$ are conjugate by the Frobenius, reflecting that $\mathrm{Gal}(\mathbb{F}_{p^2}/\mathbb{F}_p)$ has order two. It is used in the Čerednik–Drinfeld part of the development, to align a $W(\mathbb{F}_{p^2})$-structure with a prescribed one when recognising isomorphisms of rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    (a b : WittVector p (GaloisField p 2) →+* K) :
    a = b ∨
      a = b.comp (WittVector.frobenius : WittVector p (GaloisField p 2) →+* WittVector p (GaloisField p 2)) := by sorry
