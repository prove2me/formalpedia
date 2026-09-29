-- Prove2me | Theorems.Thm_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing
-- name    : WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/01478a85-0cf8-5042-8da0-a96d466c8975
-- title:
--   Teichmüller lifts of a basis form a W(k)-basis of W(l)
-- statement:
--   Let $p$ be a prime, and let $k$ and $l$ be commutative rings of characteristic $p$ which are perfect, i.e. whose Frobenius endomorphisms are bijective. Suppose $l$ is equipped with a $k$-algebra structure, with structure morphism $\operatorname{algebraMap} : k \to l$, and let $b : \iota \to l$ be a basis of $l$ as a $k$-module indexed by a finite type $\iota$. Write $W(p,\,\cdot)$ for the ring of $p$-typical Witt vectors, `WittVector.map (algebraMap k l)` for the ring homomorphism $W(k) \to W(l)$ induced functorially by the structure morphism, and `WittVector.teichmuller p` for the multiplicative Teichmüller section $l \to W(l)$. The assertion is that the map sending a family $a : \iota \to W(k)$ to $$\sum_{i \in \iota} \big(\mathrm{WittVector.map}(\mathrm{algebraMap}\ k\ l)\,(a_i)\big)\cdot \mathrm{WittVector.teichmuller}\ p\ (b_i) \in W(l)$$ is bijective as a function. Thus every Witt vector over $l$ is, in exactly one way, a $W(k)$-linear combination of the Teichmüller lifts $[b_i]$; the bijectivity is stated at the level of the underlying function, not packaged as a module isomorphism.
--
--   This is the classical freeness statement for Witt vectors of a perfect algebra: $W(l)$ is free over $W(k)$ on the Teichmüller lifts of any finite $k$-basis of $l$, the basic case being $W(\mathbb{F}_{p^f})$ free of rank $f$ over $\mathbb{Z}_p$. It is used in the project to analyse ring homomorphisms out of Witt rings of finite fields and to realise $W(\mathbb{F}_{p^2})$ and related orders by matrices over $\mathbb{Z}_p$, as in [`WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two`](thm.html#WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two) and [`WittVector.exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul`](thm.html#WittVector.exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing
    (p : ℕ) [Fact p.Prime] {k : Type u} {l : Type v} [CommRing k] [CommRing l]
    [CharP k p] [CharP l p] [PerfectRing k p] [PerfectRing l p] [Algebra k l]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι k l) :
    Function.Bijective fun a : ι → WittVector p k =>
      ∑ i, WittVector.map (algebraMap k l) (a i) * WittVector.teichmuller p (b i) := by sorry
