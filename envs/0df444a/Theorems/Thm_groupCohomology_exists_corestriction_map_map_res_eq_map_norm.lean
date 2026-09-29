-- Prove2me | Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
-- name    : groupCohomology.exists_corestriction_map_map_res_eq_map_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/f4c4efdc-5a51-5371-8870-fcd4d8a308c4
-- title:
--   Existence of corestriction satisfying the projection formula
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $S \le G$ a subgroup of finite index with $G/S$ finite; let $C$ be a $k$-linear representation of $G$ and $n$ a natural number. The assertion is that there exists an additive map $\mathrm{cor} \colon H^n(S, \mathrm{Res}_S C) \to H^n(G, C)$, where $\mathrm{Res}_S$ denotes restriction of the $G$-action along the inclusion $S \hookrightarrow G$, with the following property: for every representation $R$ of $G$, every morphism $\varphi \colon \mathrm{Res}_S R \to \mathrm{Res}_S C$ of representations of $S$, every morphism $N\varphi \colon R \to C$ of representations of $G$ such that for all $x \in R$ one has $N\varphi(x) = \sum_{g \in G/S} g \cdot \varphi(g^{-1} \cdot x)$, the sum being over the finitely many cosets with $g$ a chosen representative of each coset, and every class $z \in H^n(G, R)$, the image of $z$ under the restriction map $H^n(G,R) \to H^n(S, \mathrm{Res}_S R)$ followed by the coefficient map induced by $\varphi$ and then by $\mathrm{cor}$ equals the image of $z$ under the coefficient map $H^n(G,R) \to H^n(G,C)$ induced by $N\varphi$. Here restriction is the cohomology map along $S \hookrightarrow G$ with the identity on $\mathrm{Res}_S R$, and the coefficient maps are the cohomology maps along the identity of $S$, respectively of $G$.
--
--   This is the existence of the corestriction (transfer) in group cohomology together with the projection formula for it; with $R = C$ and $\varphi$ the identity the stated property specialises to $\mathrm{cor} \circ \mathrm{res} = [G:S]$. The map is only asserted to exist with this characterising property, not given by a cochain formula; it is used in the Herbrand-quotient computations and in the Shapiro-type corestriction statement for induced modules, and in an identity for local-global comparison maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_corestriction_map_map_res_eq_map_norm
    {k G : Type} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex] [Fintype (G ⧸ S)]
    (C : Rep k G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res S.subtype C) n →+ groupCohomology C n,
      ∀ (R : Rep k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C)
        (Nφ : R ⟶ C)
        (_ : ∀ x : R, Nφ.hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
        (z : groupCohomology R n),
        cor ((groupCohomology.map (MonoidHom.id ↥S) φ n).hom
              ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z))
          = (groupCohomology.map (MonoidHom.id G) Nφ n).hom z := by sorry
