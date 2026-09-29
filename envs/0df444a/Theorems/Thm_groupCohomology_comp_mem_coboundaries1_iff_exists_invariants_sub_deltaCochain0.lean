-- Prove2me | Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
-- name    : groupCohomology.comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/0e1531d9-1b54-5086-bc24-8ff490974260
-- title:
--   Exactness of C^G → H¹(G,A) → H¹(G,B)
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and let $A$, $B$, $C$ be $k$-linear representations of $G$ (objects of `Rep k G`), with morphisms $\varphi : A \to B$ and $\psi : B \to C$ of representations. Assume that the underlying $k$-linear map of $\varphi$ is injective, that the underlying map of $\psi$ is surjective, and that the sequence is exact in the middle in the pointwise form: for every $b \in B$ one has $\psi(b) = 0$ if and only if $b = \varphi(a)$ for some $a \in A$. Let $a$ be an element of `groupCohomology.cocycles₁ A`, i.e. an inhomogeneous $1$-cocycle $G \to A$. The assertion is that the composite $\varphi \circ a$ lies in the submodule `groupCohomology.coboundaries₁ B` of $1$-coboundaries of $B$ if and only if there is a $G$-invariant vector $c \in C$ (an element of `C.ρ.invariants`) such that $a - \delta^0(c)$ lies in `groupCohomology.coboundaries₁ A`. Here $\delta^0(c) =$ [`groupCohomology.deltaCochain₀ φ ψ hψ c`](def/GroupCohomology_ContinuousH1.html#L71) is the connecting $0$-cochain $G \to A$ attached to $c$, characterised by $\varphi(\delta^0(c)(g)) = \rho_B(g)(\sigma c) - \sigma c$ for the set-theoretic section $\sigma$ of $\psi$ obtained from its surjectivity.
--
--   This is exactness of the long exact cohomology sequence of $0 \to A \to B \to C \to 0$ at $H^1(G,A)$, stated on cocycles and coboundaries rather than on cohomology groups: the kernel of $H^1(G,A) \to H^1(G,B)$ consists exactly of the classes of connecting cochains $\delta^0(c)$ with $c \in C^G$. No continuity, smoothness or level structure enters, and the statement is used in the continuous (level-constant) setting by [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact), [`groupCohomology.finiteDimensional_continuous_of_shortExact`](thm.html#groupCohomology.finiteDimensional_continuous_of_shortExact) and [`groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero`](thm.html#groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0.lean

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

theorem groupCohomology.comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0 {k G : Type u} [CommRing k] [Group G] {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (a : groupCohomology.cocycles₁ A) :
    (φ.hom ∘ a) ∈ groupCohomology.coboundaries₁ B ↔
      ∃ c ∈ C.ρ.invariants, ((a : G → A) - groupCohomology.deltaCochain₀ φ ψ hψ c) ∈ groupCohomology.coboundaries₁ A := by sorry
