-- Prove2me | Theorems.Thm_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
-- name    : groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d4f6a8b5-83bb-590e-b5d2-405d17b13601
-- title:
--   Linearity of the connecting map on level-constant 1-cocycles
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Let $A, B, C$ be objects of `Rep k G` and let $\varphi \colon A \to B$, $\psi \colon B \to C$ be morphisms of representations such that the underlying map of $\varphi$ is injective, that of $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b = \varphi(a)$ for some $a \in A$; thus $0 \to A \to B \to C \to 0$ is exact. Assume furthermore that $B$ is smooth for $r$: for every $m \in B$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $B.\rho(s)\,m = m$ for all $s \in G$ such that $r(s)$ lies in the fixing subgroup of $F$. The assertion is that there exists a $k$-linear map $\delta$ from the module `levelCocycles₁ r C` of level-constant $1$-cocycles of $C$ to `continuousH2 r A`, the quotient of `levelCocycles₂ r A` by the submodule of those elements lying in `levelCoboundaries₂ r A`, such that for every level-constant $1$-cocycle $c$ the connecting $2$-cochain `deltaCochain₁ φ ψ hψ` of the underlying function of $c$ belongs to `levelCocycles₂ r A` and $\delta(c)$ is the class of that element under the quotient map `continuousH2π r A`.
--
--   This is the connecting homomorphism $\delta^1 \colon Z^1_{\mathrm{lc}}(G,C) \to H^2_{\mathrm{cts}}(G,A)$ of the short exact sequence $0 \to A \to B \to C \to 0$, packaged as a $k$-linear map on the module of level-constant $1$-cocycles rather than on a cohomology group. It is used in the study of the continuous long exact sequence and its dimension counts, in particular by the results on bijectivity of $\theta$ for short exact sequences, on finite-dimensionality of continuous cohomology, and in the analysis of the Kummer representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1.lean

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

theorem groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    ∃ δ : groupCohomology.levelCocycles₁ r C →ₗ[k] groupCohomology.continuousH2 r A,
      ∀ c : groupCohomology.levelCocycles₁ r C,
        ∃ h : groupCohomology.deltaCochain₁ φ ψ hψ ((c : groupCohomology.cocycles₁ C) : G → C)
            ∈ groupCohomology.levelCocycles₂ r A,
          δ c = groupCohomology.continuousH2π r A ⟨_, h⟩ := by sorry
