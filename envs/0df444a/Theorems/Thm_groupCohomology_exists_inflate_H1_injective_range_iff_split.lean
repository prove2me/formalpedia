-- Prove2me | Theorems.Thm_groupCohomology_exists_inflate_H1_injective_range_iff_split
-- name    : groupCohomology.exists_inflate_H1_injective_range_iff_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/67b66f40-87d6-5654-a9cc-71802a56472b
-- title:
--   Inflation H¹(Gal(F/ℚ),B)→ H¹(Γ,M): injective, with image the F-split classes
-- statement:
--   Let $k$ be a commutative ring and let $M$ be a $k$-linear representation of the absolute Galois group $\Gamma = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, with $\overline{\mathbb{Q}}$ the algebraic closure of $\mathbb{Q}$ realised as `AlgebraicClosure ℚ`. Let $F \subseteq \overline{\mathbb{Q}}$ be an intermediate field that is a number field and Galois over $\mathbb{Q}$, and let $B$ be a $\mathbb{Z}$-linear representation of $\mathrm{Gal}(F/\mathbb{Q})$ whose underlying module is finite. Suppose given an additive map $\beta \colon B \to M$ which is bijective and which intertwines the two actions through restriction, i.e. $\beta(\rho_B(\gamma|_F)\,b) = \rho_M(\gamma)(\beta b)$ for all $\gamma \in \Gamma$ and $b \in B$, where $\gamma \mapsto \gamma|_F$ is `AlgEquiv.restrictNormalHom`. Then there exists an additive map $\mathrm{infl} \colon H^1(\mathrm{Gal}(F/\mathbb{Q}), B) \to H^1(\Gamma, M)$ with three properties. First, it is pinned at cocycle level: whenever $n$ is a $1$-cocycle for $B$ and $ny$ a $1$-cocycle for $M$ satisfying $ny(\gamma) = \beta(n(\gamma|_F))$ for all $\gamma \in \Gamma$, the class of $n$ under `H1π B` is sent to the class of $ny$ under `H1π M`. Second, $\mathrm{infl}$ is injective. Third, a class $y \in H^1(\Gamma, M)$ lies in the range of $\mathrm{infl}$ if and only if $y$ is the class of some $1$-cocycle $ny$ for $M$ which satisfies $ny(\gamma s) = ny(\gamma)$ for all $\gamma \in \Gamma$ and all $s$ in the fixing subgroup of $F$, and $ny(s) = 0$ for all such $s$.
--
--   This is the inflation part of the inflation–restriction sequence for the normal subgroup $\mathrm{Gal}(\overline{\mathbb{Q}}/F) \subseteq \Gamma$, packaged so that consumers may work with explicit cocycles: injectivity of inflation in degree one, together with the description of its image as the classes represented by cocycles that factor through $\mathrm{Gal}(F/\mathbb{Q})$. It is used in the construction of classes in the continuous $H^1$ of a Selmer-type condition and in the statement of nondegeneracy of the pairing between the relevant $\text{Ш}^1$ and $\text{Ш}^2$ groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_inflate_H1_injective_range_iff_split.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_inflate_H1_injective_range_iff_split
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M) (hβ : Function.Bijective β)
    (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
      β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = M.ρ γ (β b)) :
    ∃ infl : groupCohomology B 1 →+ H1 M,
      (∀ (n : cocycles₁ B) (ny : cocycles₁ M),
        (∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
          infl ((H1π B).hom n) = (H1π M).hom ny) ∧
      Function.Injective infl ∧
      (∀ y : H1 M, (∃ x, infl x = y) ↔
        ∃ ny : cocycles₁ M, (H1π M).hom ny = y ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) := by sorry
