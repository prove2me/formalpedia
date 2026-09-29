-- Prove2me | Theorems.Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
-- name    : WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5d48586f-1c00-5b26-ac42-075d53732972
-- title:
--   Ring maps W(𝔽_{p²})→ W(k) differ by Frobenius
-- statement:
--   Let $p$ be a prime and let $k$ be a field of characteristic $p$ that is perfect in the sense that the $p$-power map on $k$ is bijective (`PerfectRing k p`). Consider the ring of $p$-typical Witt vectors $W(\mathbb{F}_{p^2})$ of the Galois field `GaloisField p 2` with $p^2$ elements, and the ring $W(k)$ of $p$-typical Witt vectors of $k$. The assertion is that for any two ring homomorphisms $a, b \colon W(\mathbb{F}_{p^2}) \to W(k)$, either $a = b$, or $a$ is the composite of the Witt vector Frobenius endomorphism `WittVector.frobenius` of $W(\mathbb{F}_{p^2})$ followed by $b$, that is $a = b \circ \sigma$ with $\sigma$ the ring endomorphism of $W(\mathbb{F}_{p^2})$ induced by $x \mapsto x^p$ on $\mathbb{F}_{p^2}$. No surjectivity, injectivity or continuity hypothesis is imposed on $a$ and $b$; the two alternatives are not claimed to be exclusive. Since $\sigma$ has order two on $W(\mathbb{F}_{p^2})$, the disjunction is symmetric in $a$ and $b$ up to replacing $b$ by $b \circ \sigma$.
--
--   This is the rigidity statement that the unramified quadratic extension $W(\mathbb{F}_{p^2}) = \mathbb{Z}_{p^2}$ admits at most two ring maps into the Witt vectors of a perfect field of characteristic $p$, the two differing by the nontrivial element of $\mathrm{Gal}(\mathbb{F}_{p^2}/\mathbb{F}_p)$. It is used in the Cherednik–Drinfeld part of the development, in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.comp_frobenius_of_isPiTranslate`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.comp_frobenius_of_isPiTranslate), to compare two Cartier-module structures; the proof rests on the fact that $W(\mathbb{F}_{p^2})$ is free of rank two over $W(\mathbb{F}_p)$ on Teichmüller representatives ([`WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing`](thm.html#WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (a b : WittVector p (GaloisField p 2) →+* WittVector p k) :
    a = b ∨
      a = b.comp (WittVector.frobenius : WittVector p (GaloisField p 2) →+* WittVector p (GaloisField p 2)) := by sorry
