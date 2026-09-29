-- Prove2me | Theorems.Thm_integralClosure_isAlgClosed_of_surjective
-- name    : integralClosure.isAlgClosed_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/370a0ea0-927b-59c6-a427-f80d6156a975
-- title:
--   Quotients of an integral closure in an algebraically closed field
-- statement:
--   Let $R$ be a commutative ring, let $L$ be an algebraically closed field carrying an $R$-algebra structure, and let $F$ be a field. Write $A =$ `integralClosure R L` for the subalgebra of $L$ consisting of the elements of $L$ integral over $R$. The assertion is that if there exists a surjective ring homomorphism $\varphi \colon A \to F$, then $F$ is algebraically closed (in Mathlib's sense: every non-constant polynomial over $F$ has a root in $F$). No hypothesis is imposed on the kernel of $\varphi$ beyond its being the kernel of a map to a field, and no finiteness or domain assumption is made on $R$; in particular, applied to the quotient maps $A \to A/\mathfrak{q}$ at maximal ideals $\mathfrak{q}$, it says that every residue field of $A$ at a maximal ideal is algebraically closed, and, for $R = \mathbb{Z}$ and $L = \mathbb{C}$, that $\overline{\mathbb{Z}}/\mathfrak{q}$ is algebraically closed for every maximal ideal $\mathfrak{q}$.
--
--   This is the standard fact that the residue fields of the ring of all integers of $R$ in an algebraically closed field are again algebraically closed, for instance that $\overline{\mathbb{Z}}/\mathfrak{q}$ is an algebraic closure of $\mathbb{F}_p$. It is used in comparing reductions of algebraic integers, in [`CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_ringHom_integralClosure`](thm.html#CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_ringHom_integralClosure), where characteristic polynomials of Frobenius are transported along a ring homomorphism out of an integral closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integralClosure_isAlgClosed_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem integralClosure.isAlgClosed_of_surjective
    {R L F : Type*} [CommRing R] [Field L] [IsAlgClosed L] [Algebra R L] [Field F]
    (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
    IsAlgClosed F := by sorry
