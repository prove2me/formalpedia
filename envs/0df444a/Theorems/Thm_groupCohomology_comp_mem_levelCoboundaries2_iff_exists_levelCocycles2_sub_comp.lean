-- Prove2me | Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
-- name    : groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/372e7854-5c89-5b3e-aa2c-5e1d99e55151
-- title:
--   Exactness at H² in level-constant cochains, smooth B
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, used to define the level subgroups $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ for $F$ a finite-dimensional intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$. Let $A, B, C$ be $k$-linear representations of $G$ and $\varphi \colon A \to B$, $\psi \colon B \to C$ morphisms of representations such that the underlying linear map of $\varphi$ is injective, that of $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b = \varphi(a)$ for some $a \in A$. Assume further that $B$ is smooth in the pointwise sense: each $m \in B$ admits a finite-dimensional intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $B.\rho(s)\,m = m$ for all $s$ with $r(s)$ in the fixing subgroup of $F$. Let $b \colon G \times G \to B$ lie in [`groupCohomology.levelCocycles₂ r B`](def/GroupCohomology_ContinuousH2.html#L85), that is, $b$ is an inhomogeneous $2$-cocycle satisfying the level-constancy condition `IsLevelConstant₂ r`. The conclusion is an equivalence: the composite $\psi \circ b$ lies in [`groupCohomology.levelCoboundaries₂ r C`](def/GroupCohomology_ContinuousH2.html#L92) (the coboundaries of level-constant $1$-cochains of $C$) if and only if there exists $a \in$ [`groupCohomology.levelCocycles₂ r A`](def/GroupCohomology_ContinuousH2.html#L85) with $b - \varphi \circ a \in$ [`groupCohomology.levelCoboundaries₂ r B`](def/GroupCohomology_ContinuousH2.html#L92). No smoothness hypothesis is imposed on $A$ or $C$.
--
--   This is the cochain-level form of exactness of the continuous cohomology sequence at $H^2(G,B)$ for a short exact sequence $0 \to A \to B \to C \to 0$ of smooth $B$, with continuity encoded by level-constancy of cochains relative to $r$ rather than by a topology. It is used in assembling the continuous long exact sequence and its consequences, among them the statements identifying kernels and images of the induced map on $H^2$ for Kummer-type representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp.lean

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

theorem groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    (b : G × G → B) (hb : b ∈ groupCohomology.levelCocycles₂ r B) :
    (ψ.hom ∘ b) ∈ groupCohomology.levelCoboundaries₂ r C ↔
      ∃ a ∈ groupCohomology.levelCocycles₂ r A, (b - φ.hom ∘ a) ∈ groupCohomology.levelCoboundaries₂ r B := by sorry
