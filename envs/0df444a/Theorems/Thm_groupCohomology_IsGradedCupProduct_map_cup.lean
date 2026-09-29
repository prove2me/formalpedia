-- Prove2me | Theorems.Thm_groupCohomology_IsGradedCupProduct_map_cup
-- name    : groupCohomology.IsGradedCupProduct.map_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a87c3bf0-578b-52fa-b37e-ba1338cffa16
-- title:
--   Functoriality of graded cup products under (f,φ⊗ψ)
-- statement:
--   Let $k$ be a commutative ring, $G$ and $H$ groups, $f : H \to G$ a group homomorphism, $A,B$ representations of $G$ over $k$ and $A',B'$ representations of $H$ over $k$, together with morphisms of $H$-representations $\varphi : f^{*}A \to A'$ and $\psi : f^{*}B \to B'$. Let $\mathrm{cup}$ be a family of $k$-bilinear maps $H^{p}(G,A) \times H^{q}(G,B) \to H^{p+q}(G,A\otimes B)$ and $\mathrm{cup}'$ a family $H^{p}(H,A') \times H^{q}(H,B') \to H^{p+q}(H,A'\otimes B')$, each assumed to satisfy `IsGradedCupProduct`: whenever $x$ is a $p$-cocycle and $y$ a $q$-cocycle, and the inhomogeneous differential annihilates the cochain-level cup product $\sigma \mapsto x(\sigma_{1},\dots,\sigma_{p}) \otimes \rho_{B}(\sigma_{1}\cdots\sigma_{p})\,y(\sigma_{p+1},\dots,\sigma_{p+q})$, then the value of the family on the classes of $x$ and $y$ is the class of that cochain. Then for all $p,q \in \mathbb{N}$, $x \in H^{p}(G,A)$ and $y \in H^{q}(G,B)$, the map induced on cohomology by $f$ together with $\varphi \otimes \psi : f^{*}(A\otimes B) \to A'\otimes B'$ sends $\mathrm{cup}\,p\,q\,x\,y$ to $\mathrm{cup}'\,p\,q$ applied to the images of $x$ and $y$ under the maps induced by $(f,\varphi)$ and $(f,\psi)$.
--
--   This is the functoriality of the cup product in group cohomology, stated for an arbitrary pair of families satisfying the cocycle-level characterisation: taking $f = \mathrm{id}$ it gives naturality in both variables, and taking $f$ the inclusion of a subgroup with $\varphi,\psi$ the identities it gives $\mathrm{res}(x \cup y) = \mathrm{res}\,x \cup \mathrm{res}\,y$. It is used in the construction of the Tate cup product, [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_IsGradedCupProduct_map_cup.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 600000
universe u
open CategoryTheory MonoidalCategory groupCohomology

theorem groupCohomology.IsGradedCupProduct.map_cup {k G H : Type u} [CommRing k] [Group G] [Group H]
    (f : H →* G) {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (ψ : Rep.res f B ⟶ B')
    (cup : groupCohomology.GradedCupFamily A B) (hcup : groupCohomology.IsGradedCupProduct A B cup)
    (cup' : groupCohomology.GradedCupFamily A' B') (hcup' : groupCohomology.IsGradedCupProduct A' B' cup')
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology B q) :
    (groupCohomology.map f (φ ⊗ₘ ψ : Rep.res f (A ⊗ B) ⟶ A' ⊗ B') (p + q)).hom (cup p q x y)
      = cup' p q ((groupCohomology.map f φ p).hom x) ((groupCohomology.map f ψ q).hom y) := by sorry
