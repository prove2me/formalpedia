-- Prove2me | Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
-- name    : groupCohomology.comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4fd458b2-4994-5dcd-8e66-bf871228486b
-- title:
--   Exactness at H¹(B) for level-constant cochains
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a group homomorphism into the automorphism group of an algebraic closure of $\mathbb{Q}$ over $\mathbb{Q}$. Let $A, B, C$ be $k$-linear representations of $G$ and let $\varphi \colon A \to B$, $\psi \colon B \to C$ be morphisms of representations such that $\varphi$ is injective on underlying modules, $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b$ lies in the image of $\varphi$. Assume $B$ is pointwise smooth for $r$: for every $m \in B$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\rho_B(s)m = m$ for all $s$ with $r(s)$ in the fixing subgroup of $F$. Finally let $b$ be an inhomogeneous $1$-cocycle of $B$ (an element of the kernel of $d^{1,2}_B$) satisfying `IsLevelConstant₁ r`, i.e. there is a finite subextension $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that $b$ is unchanged when its argument is translated on the right by any $s$ with $r(s)$ fixing $F$. The assertion is that $\psi \circ b$ lies in $\operatorname{coboundaries}_1(C)$, the image of $c \mapsto (g \mapsto \rho_C(g)c - c)$, if and only if there exists a $1$-cocycle $a$ of $A$ satisfying `IsLevelConstant₁ r` with $b - \varphi \circ a \in \operatorname{coboundaries}_1(B)$.
--
--   This is exactness at the middle term of the long exact sequence in continuous (level-constant) cohomology attached to a short exact sequence $0 \to A \to B \to C \to 0$ of smooth representations, in the sharpened form that a cocycle of $B$ whose image is a coboundary in $C$ may be adjusted by a coboundary of $B$ so as to come from a level-constant cocycle of $A$. It is used in the construction and analysis of the continuous $H^1$–$H^2$ maps, in particular by [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact), [`groupCohomology.finiteDimensional_continuous_of_shortExact`](thm.html#groupCohomology.finiteDimensional_continuous_of_shortExact) and [`groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero`](thm.html#groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp.lean

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

theorem groupCohomology.comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    (b : groupCohomology.cocycles₁ B) (hb : groupCohomology.IsLevelConstant₁ r b) :
    (ψ.hom ∘ b) ∈ groupCohomology.coboundaries₁ C ↔
      ∃ a : groupCohomology.cocycles₁ A, groupCohomology.IsLevelConstant₁ r a ∧
        ((b : G → B) - φ.hom ∘ a) ∈ groupCohomology.coboundaries₁ B := by sorry
