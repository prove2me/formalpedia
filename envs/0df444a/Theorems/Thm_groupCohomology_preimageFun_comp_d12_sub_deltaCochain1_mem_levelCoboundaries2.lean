-- Prove2me | Theorems.Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
-- name    : groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/89db9805-377b-5a75-8cf1-c793ae9ecef0
-- title:
--   Connecting 2-cochain is independent of the chosen lift
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ a homomorphism into the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`. Let $A, B, C$ be objects of `Rep k G` and $\varphi \colon A \to B$, $\psi \colon B \to C$ morphisms of representations such that the underlying map of $\varphi$ is injective, that of $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b$ lies in the image of $\varphi$; thus $A \to B \to C$ is a short exact sequence of $k[G]$-modules. Let $c$ be an element of `cocycles₁ C`, i.e. a $1$-cochain $G \to C$ killed by $d_{12}$, and assume $c$ satisfies `IsLevelConstant₁ r` (the finite-level constancy condition: there is a finite subextension $F$ of $\overline{\mathbb Q}/\mathbb Q$ such that the value of the cochain is unchanged when its argument is altered by an element $s$ with $r(s)$ in the fixing subgroup of $F$). Let $L \colon G \to B$ be any function satisfying the same condition `IsLevelConstant₁ r` and lifting $c$, i.e. $\psi(L(g)) = c(g)$ for all $g$; no cocycle condition on $L$ is imposed. Then the $2$-cochain $\mathrm{preimageFun}_\varphi \circ d_{12}(L) - \delta^1_{\varphi,\psi}(c)$, where `preimageFun φ` sends $b \in B$ to a chosen $\varphi$-preimage when one exists and to $0$ otherwise and `deltaCochain₁ φ ψ hψ c` is the connecting $2$-cochain attached to $c$ via the chosen set-theoretic section of $\psi$, belongs to `levelCoboundaries₂ r A`; by `mem_levelCoboundaries₂_iff` this means it is $d_{12}$ of a $1$-cochain $G \to A$ satisfying `IsLevelConstant₁ r`.
--
--   This is the independence statement for the connecting map on level-constant cohomology: the class of the connecting $2$-cochain attached to a level-constant $1$-cocycle $c$ may be computed from an arbitrary level-constant lift of $c$, not only from the lift provided by the fixed section of $\psi$. It is used in the construction and analysis of the boundary map in continuous degree-two cohomology, notably by [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact), [`groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal`](thm.html#groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal) and [`groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero`](thm.html#groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2.lean

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

theorem groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (c : groupCohomology.cocycles₁ C) (hc : groupCohomology.IsLevelConstant₁ r c)
    (L : G → B) (hL : groupCohomology.IsLevelConstant₁ r L) (hLc : ∀ g, ψ.hom (L g) = c g) :
    (groupCohomology.preimageFun φ ∘ (groupCohomology.d₁₂ B).hom L - groupCohomology.deltaCochain₁ φ ψ hψ c)
      ∈ groupCohomology.levelCoboundaries₂ r A := by sorry
