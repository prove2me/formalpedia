-- Prove2me | Theorems.Thm_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
-- name    : WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/f499ee48-a9c7-522a-b5f3-e9ee791ddc54
-- title:
--   Unique lifting of W(k) along square-zero surjections
-- statement:
--   Let $p$ be a prime and let $k$ be a field of characteristic $p$ which is perfect in the sense of carrying a `PerfectRing` structure for $p$. Let $B$ and $B_0$ be commutative rings (in the same universe as $k$) and let $q : B \to B_0$ be a ring homomorphism subject to three hypotheses: $q$ is surjective; any two elements $s, t \in B$ with $q s = 0$ and $q t = 0$ satisfy $s t = 0$, i.e. the kernel of $q$ has square zero; and the image of $p$ in $B$ is nilpotent. Then for every ring homomorphism $\psi_0 : W(k) \to B_0$ from the ring of $p$-typical Witt vectors of $k$ there is a unique ring homomorphism $\psi : W(k) \to B$ with $q \circ \psi = \psi_0$, the composite being taken as `q.comp ψ`. Note that nilpotence of $p$ is required in $B$ only, and that no flatness or $p$-torsion-freeness assumption is placed on $B$ or $B_0$.
--
--   This is the formal étaleness (indeed, formal smoothness together with formal unramifiedness) of $W(k)$ over $\mathbb{Z}$ relative to square-zero thickenings of rings in which $p$ is nilpotent, in the shape of a unique infinitesimal lifting property. It is used for the construction of ring homomorphisms out of $W(k)$ by successive infinitesimal lifting, in particular by [`CerednikDrinfeld.FormalOmega.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalOmega.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent) and by [`WittVector.ringHom_comp_eq_comp_frobenius_of_sub_pow_mem_of_isHausdorff`](thm.html#WittVector.ringHom_comp_eq_comp_frobenius_of_sub_pow_mem_of_isHausdorff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open WittVector

theorem WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B B₀ : Type u) [CommRing B] [CommRing B₀] (q : B →+* B₀) (hq : Function.Surjective q)
    (hsq : ∀ s t : B, q s = 0 → q t = 0 → s * t = 0) (hpB : IsNilpotent (p : B))
    (ψ₀ : WittVector p k →+* B₀) :
    ∃! ψ : WittVector p k →+* B, q.comp ψ = ψ₀ := by sorry
