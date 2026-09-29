-- Prove2me | Theorems.Thm_WittVector_ringHom_ext_padicInt
-- name    : WittVector.ringHom_ext_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/338fd580-c690-559f-95a4-f8871257ff39
-- title:
--   Uniqueness of ring maps ℤₚ → W(R) in characteristic p
-- statement:
--   Let $p$ be a natural number which is prime, and let $R$ be a commutative ring of characteristic $p$ (that is, carrying a `CharP R p` instance), living in an arbitrary universe. Let $W(R) =$ `WittVector p R` be the ring of $p$-typical Witt vectors over $R$. The assertion is that any two ring homomorphisms $f, g \colon \mathbb{Z}_p \to W(R)$ from the ring of $p$-adic integers into $W(R)$ are equal as bundled ring homomorphisms, $f = g$. No hypothesis is imposed on $R$ beyond commutativity and characteristic $p$; in particular $R$ need not be perfect, reduced, local, or a field, and no topology or continuity assumption is placed on $f$ or $g$. Equivalently, $W(R)$ admits at most one $\mathbb{Z}_p$-algebra structure, so that the canonical one is the only one.
--
--   This is the standard uniqueness of the $\mathbb{Z}_p$-algebra structure on the Witt vectors of a ring of characteristic $p$. It is used so that statements quantifying over an arbitrary ring map $\mathbb{Z}_p \to W(K)$ may be reduced to the canonical structure map; in this development it is cited in the Cherednik–Drinfeld material on special formal $\mathcal{O}$-modules, in the lemmas [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node) and [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_ringHom_ext_padicInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

universe u

theorem WittVector.ringHom_ext_padicInt
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    (f g : ℤ_[p] →+* WittVector p R) : f = g := by sorry
