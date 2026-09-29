-- Prove2me | Theorems.Thm_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
-- name    : WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/dc7f0e6b-7c2d-5e91-9b88-37f5a3e234f6
-- title:
--   Frobenius-fixed Witt vectors map canonically when p is nilpotent
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring in which the image of $p$ is nilpotent, and let $A$ be a ring equipped with an $R$-algebra structure. Write $\mathbb{Z}_{p^2} =$ `Zp2 p` for the ring $\mathrm{W}(\mathbb{F}_{p^2})$ of $p$-typical Witt vectors over the Galois field `GaloisField p 2` with $p^2$ elements. Let $\rho : \mathbb{Z}_{p^2} \to A$ and $j : \mathbb{Z}_{p^2} \to R$ be arbitrary ring homomorphisms, subject to no compatibility condition whatsoever, and let $a \in \mathbb{Z}_{p^2}$ be fixed by the Witt vector Frobenius, i.e. `WittVector.frobenius a = a`. Then $\rho(a)$ equals the image of $j(a)$ under the structure map $R \to A$. In other words, on the Frobenius-fixed subring of $\mathrm{W}(\mathbb{F}_{p^2})$ the two homomorphisms $\rho$ and $\mathrm{algebraMap}\,R\,A \circ j$ agree, the point being that a Frobenius-fixed Witt vector is, modulo any power of $p$ that already vanishes in $R$, a natural number, and natural numbers are sent to the same element of $A$ by both maps.
--
--   The statement records the rigidity of the unramified quadratic extension $\mathrm{W}(\mathbb{F}_{p^2})$ of $\mathbb{Z}_p$ in the presence of nilpotence of $p$: on $\sigma$-fixed elements, that is on the copy of $\mathbb{Z}_p$ inside it, any two ring homomorphisms into an $R$-algebra and into $R$ induce the same element of $A$. It is used in the theory of special formal modules, namely in [`CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent), where the $\mathbb{Z}_{p^2}$-action on a formal module must be compared with the structural scalars of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CerednikDrinfeld

theorem WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (hp : IsNilpotent (p : R))
    {A : Type v} [Ring A] [Algebra R A]
    (ρ : Zp2 p →+* A) (j : Zp2 p →+* R) (a : Zp2 p) (ha : WittVector.frobenius a = a) :
    ρ a = algebraMap R A (j a) := by sorry
