-- Prove2me | Theorems.Thm_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
-- name    : integralClosure.isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d1a07c15-1dec-58f2-ab7a-a74bef4b368c
-- title:
--   Transitive automorphism action on maximal ideals forces local normalisation
-- statement:
--   Let $R$ be a commutative domain, $F$ a field which is a fraction field of $R$ (via the given $R$-algebra structure), and $L$ a field equipped with $F$-algebra and $R$-algebra structures forming a scalar tower over $R$, with $L$ finite-dimensional over $F$. Write $B = \mathrm{integralClosure}\,R\,L$ for the integral closure of $R$ in $L$ and $\tilde R = \mathrm{integralClosure}\,R\,F$ for the integral closure of $R$ in $F$. Assume that the group $L \simeq_{\mathrm{alg}[F]} L$ of $F$-algebra automorphisms of $L$ acts transitively on maximal ideals of $B$ in the following precise sense: for all ideals $M_1, M_2$ of $B$ that are maximal there exists an $F$-automorphism $\sigma$ of $L$ such that $M_2$ is the preimage of $M_1$ under the restriction of $\sigma$ to $B$, the latter being Mathlib's `galRestrict R F L ↥(integralClosure R L) σ`. The conclusion is that $\tilde R$ is a local ring in the sense of `IsLocalRing`: it is nontrivial and has a unique maximal ideal.
--
--   This is a descent statement for locality of the normalisation: transitivity of the automorphism action on the maximal ideals of the integral closure upstairs (automatic in the classical Galois situation, where the decomposition groups act transitively on primes over a fixed prime) forces the integral closure of $R$ in $F$ to be local. It is used in the proof of [`Subring.eq_of_isMaximal_of_marked_galois_descent`](thm.html#Subring.eq_of_isMaximal_of_marked_galois_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem integralClosure.isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
    {R F L : Type*} [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L]
    (htrans : ∀ M₁ M₂ : Ideal ↥(integralClosure R L), M₁.IsMaximal → M₂.IsMaximal →
      ∃ σ : L ≃ₐ[F] L, M₂ = Ideal.comap (galRestrict R F L ↥(integralClosure R L) σ) M₁) :
    IsLocalRing ↥(integralClosure R F) := by sorry
