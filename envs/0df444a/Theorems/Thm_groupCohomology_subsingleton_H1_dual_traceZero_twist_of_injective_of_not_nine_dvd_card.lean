-- Prove2me | Theorems.Thm_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
-- name    : groupCohomology.subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/bcbc0b2a-87b6-532d-bb55-6b89a5eb45d2
-- title:
--   Vanishing of H¹ with twisted dual trace-zero coefficients, characteristic 3
-- statement:
--   Let $k$ be a finite field of characteristic $3$, let $V$ be a $k$-vector space with $\dim_k V = 2$, and let $Q$ be a finite group with $9 \nmid \#Q$. Let $\sigma \colon Q \to \mathrm{End}_k(V)$ be an injective monoid homomorphism (so each $\sigma(q)$ is invertible, and $\sigma$ is a faithful representation of $Q$ on $V$), and let $\chi \colon Q \to (\mathbb{Z}/3)^{\times}$ be any group homomorphism. Write $M_0 = \ker(\mathrm{tr}_{k,V}) \subseteq \mathrm{End}_k(V)$ for the trace-zero endomorphisms, regarded as a module over $\mathbb{Z}/3$. Let $A$ be a representation of $Q$ over $\mathbb{Z}/3$ together with a $\mathbb{Z}/3$-linear isomorphism $e \colon A \to \mathrm{Hom}_{\mathbb{Z}/3}(M_0, \mathbb{Z}/3)$ which intertwines the action as follows: for all $q \in Q$, $a \in A$ and all $X, Y \in M_0$ with $Y = \sigma(q)^{-1} X \sigma(q)$ in $\mathrm{End}_k(V)$, one has $e(\rho_A(q)a)(X) = \chi(q)\, e(a)(Y)$. Then $H^1(Q, A)$ is a subsingleton, i.e. it vanishes.
--
--   This is the characteristic-$3$ vanishing statement for the $\chi$-twisted $\mathbb{F}_3$-dual of the adjoint (conjugation) action on trace-zero endomorphisms of a plane, the case of a faithful plane representation whose order is divisible by at most one factor of $3$; it corresponds to the residue characteristic $3$ case in the proof of Theorem 2.49 of Darmon–Diamond–Taylor. It is used by [`groupCohomology.H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range`](thm.html#groupCohomology.H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range), and its proof cites the vanishing of $H^1$ of a finite group whose order is invertible in the coefficient ring, [`groupCohomology.subsingleton_H1_of_isUnit_card`](thm.html#groupCohomology.subsingleton_H1_of_isUnit_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open groupCohomology

theorem groupCohomology.subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
    {k : Type} [Field k] [Finite k] [CharP k 3]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {Q : Type} [Group Q] [Finite Q] (h9 : ¬ 9 ∣ Nat.card Q)
    (σ : Q →* Module.End k V) (hσ : Function.Injective σ)
    (χ : Q →* (ZMod 3)ˣ)
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep (ZMod 3) Q)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (q : Q) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ q⁻¹ * X * σ q → e (A.ρ q a) X = (χ q : ZMod 3) * e a Y) :
    Subsingleton (H1 A) := by sorry
