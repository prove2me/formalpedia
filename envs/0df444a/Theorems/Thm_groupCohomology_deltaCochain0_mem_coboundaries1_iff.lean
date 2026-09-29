-- Prove2me | Theorems.Thm_groupCohomology_deltaCochain0_mem_coboundaries1_iff
-- name    : groupCohomology.deltaCochain0_mem_coboundaries1_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/accbd74f-98bd-5885-8321-3b9f3642cbf4
-- title:
--   Exactness at C^G of the connecting sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$, $B$, $C$ be representations of $G$ over $k$, with morphisms of representations $\varphi : A \to B$ and $\psi : B \to C$. Assume the underlying $k$-linear map of $\varphi$ is injective, the underlying map of $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b = \varphi(a)$ for some $a \in A$. Let $c \in C$ be invariant, i.e. $\rho_C(g)c = c$ for all $g \in G$. Write $\sigma$ for the set-theoretic section of $\psi$ determined by the surjectivity hypothesis, and let $\delta^0(c)$ be the connecting $1$-cochain $G \to A$ characterised by $\varphi(\delta^0(c)(g)) = \rho_B(g)(\sigma c) - \sigma c$. The assertion is an equivalence: $\delta^0(c)$ lies in the submodule of $1$-coboundaries of $A$, that is, there is $a_0 \in A$ with $\delta^0(c)(g) = \rho_A(g)a_0 - a_0$ for all $g$, if and only if there exists an invariant $b \in B$ with $\psi(b) = c$.
--
--   This is exactness of $B^G \to C^G \to H^1(G,A)$ at $C^G$ for a short exact sequence of $G$-representations, in the explicit cochain form needed later: the class of $\delta^0(c)$ vanishes exactly when $c$ lifts to an invariant of $B$. No continuity, smoothness or level structure enters at this point; the result is used in the construction of the connecting map on continuous cohomology and its exactness properties, being cited by [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact), [`groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero`](thm.html#groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero) and [`groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective`](thm.html#groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_deltaCochain0_mem_coboundaries1_iff.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.deltaCochain0_mem_coboundaries1_iff {k G : Type u} [CommRing k] [Group G] {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (c : C) (hc : c ∈ C.ρ.invariants) :
    groupCohomology.deltaCochain₀ φ ψ hψ c ∈ groupCohomology.coboundaries₁ A ↔
      ∃ b ∈ B.ρ.invariants, ψ.hom b = c := by sorry
