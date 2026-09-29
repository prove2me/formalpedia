-- Prove2me | Theorems.Thm_integralClosure_moduleFinite_of_isReduced_of_charZero
-- name    : integralClosure.moduleFinite_of_isReduced_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/1029811c-9b19-54eb-afbd-c5dc66a754e9
-- title:
--   Finiteness of the integral closure in a finite reduced algebra
-- statement:
--   Let $R$ be a commutative ring which is a domain, Noetherian, and integrally closed in its field of fractions; let $K$ be a field of characteristic zero equipped with an $R$-algebra structure making it a fraction field of $R$; and let $L$ be a commutative ring which is reduced (its only nilpotent element is $0$), equipped with a $K$-algebra structure under which $L$ is a finitely generated $K$-module, together with an $R$-algebra structure compatible with those of $K$ over $R$ and of $L$ over $K$ (a scalar tower $R \to K \to L$). The assertion is that the integral closure of $R$ in $L$, that is the $R$-subalgebra `integralClosure R L` of those elements of $L$ satisfying a monic polynomial equation with coefficients in $R$, is a finitely generated $R$-module. No separability, flatness or domain hypothesis is imposed on $L$ itself: reducedness together with finiteness over a field of characteristic zero suffices.
--
--   This is the classical finiteness of the maximal order: the integral closure of a Noetherian integrally closed domain in a finite reduced algebra over its characteristic-zero fraction field is module-finite. It is used to show that increasing chains of $R$-subalgebras of $L$ contained in the integral closure stabilise ([`Subalgebra.exists_forall_le_eq_of_monotone_of_le_integralClosure`](thm.html#Subalgebra.exists_forall_le_eq_of_monotone_of_le_integralClosure)), the form in which the statement enters Tate's study of $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integralClosure_moduleFinite_of_isReduced_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem integralClosure.moduleFinite_of_isReduced_of_charZero
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [CommRing L] [IsReduced L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) := by sorry
