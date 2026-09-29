-- Prove2me | Theorems.Thm_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
-- name    : exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/44f65c86-f8db-5c6d-8b11-dcde77fa3832
-- title:
--   Divisibility detected up to a bounded defect
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $\varpi \in R$ be an irreducible element. Let $A$ be a commutative $R$-algebra, and let $M$ be an abelian group carrying compatible $R$- and $A$-module structures, the $R$-action being the one induced through $A$ (a scalar tower), such that $M$ is finitely generated over $R$ and has no zero smul-divisors over $R$, i.e. $r \cdot x = 0$ with $r \in R$, $x \in M$ forces $r = 0$ or $x = 0$. Assume the action of $A$ on $M$ is faithful in the sense that any $t \in A$ with $t \cdot x = 0$ for all $x \in M$ is zero. The conclusion asserts the existence of a single natural number $b$, depending only on these data, such that for every natural number $m$ and every $t \in A$: if for each $x \in M$ there is some $y \in M$ with $t \cdot x = \varpi^{m+b} \cdot y$ — that is, $tM \subseteq \varpi^{m+b} M$ — then there is $t' \in A$ with $t = \varpi^{m} \cdot t'$, the scalar action of $R$ on $A$. Note that the defect $b$ is uniform in $m$ and $t$.
--
--   An elementary piece of commutative algebra over a discrete valuation ring: a faithful order $A$ inside $\operatorname{End}_R(M)$ need not be saturated, but the failure is bounded, so divisibility of $tM$ by $\varpi^{m+b}$ forces divisibility of $t$ by $\varpi^{m}$ in $A$. It is used in the Hecke-algebra arguments on the Tate module of a modular Jacobian, being cited by [`ModularCurve.exists_generator_tateModule_inf_pi_closure_inertia_smul_sub_and_smul_eisensteinTorsionBar_eq_zero`](thm.html#ModularCurve.exists_generator_tateModule_inf_pi_closure_inertia_smul_sub_and_smul_eisensteinTorsionBar_eq_zero) and by [`ModularCurve.exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero`](thm.html#ModularCurve.exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ)
    {A : Type} [CommRing A] [Algebra R A]
    {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [NoZeroSMulDivisors R M]
    (hfaith : ∀ t : A, (∀ x : M, t • x = 0) → t = 0) :
    ∃ b : ℕ, ∀ (m : ℕ) (t : A), (∀ x : M, ∃ y : M, t • x = ϖ ^ (m + b) • y) →
      ∃ t' : A, t = ϖ ^ m • t' := by sorry
