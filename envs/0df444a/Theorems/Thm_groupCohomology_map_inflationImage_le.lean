-- Prove2me | Theorems.Thm_groupCohomology_map_inflationImage_le
-- name    : groupCohomology.map_inflationImage_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6ad0d127-02e6-579e-b603-6bdedc125475
-- title:
--   Inflation images are carried into inflation images
-- statement:
--   Let $k$ be a commutative ring, let $f \colon \Delta \to G$ be a homomorphism of groups, let $M$ be a $k$-linear representation of $G$ and $N$ a $k$-linear representation of $\Delta$, and let $\varphi \colon \mathrm{res}_f M \to N$ be a morphism of $k$-linear $\Delta$-representations from the restriction of $M$ along $f$ to $N$. Let $T$ be a normal subgroup of $G$ and $S$ a normal subgroup of $\Delta$ with $S \le f^{-1}(T)$. Write $\mathrm{inflationImage}\,M\,T$ for the $k$-submodule of $H^1(G, M)$ that is the range of the $k$-linear map underlying `groupCohomology.map (QuotientGroup.mk' T) (Rep.ofHom (M.ρ.quotientToInvariants_lift T)) 1`, i.e. the image of the inflation map $H^1(G/T, M^{T}) \to H^1(G, M)$ attached to the projection $G \to G/T$ and the natural map from $M^{T}$ with its $G/T$-action to $M$, and similarly $\mathrm{inflationImage}\,N\,S \subseteq H^1(\Delta, N)$. Then the image of $\mathrm{inflationImage}\,M\,T$ under the $k$-linear map underlying `groupCohomology.map f φ 1 : H¹(G, M) ⟶ H¹(Δ, N)` is contained in $\mathrm{inflationImage}\,N\,S$.
--
--   This is the functoriality of inflation in the pair $(f, \varphi)$, at the level of the submodules of $H^1$ inflated from quotients: compatibility of the map on $H^1$ induced by a group homomorphism and a morphism of representations with the subspaces of classes inflated from $G/T$, respectively $\Delta/S$. It is used to prove [`groupCohomology.inflationImage_antitone`](thm.html#groupCohomology.inflationImage_antitone), the antitonicity of the inflation image in the normal subgroup, which is the case $\Delta = G$, $f = \mathrm{id}$, $N = M$, $\varphi = \mathrm{id}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_inflationImage_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.map_inflationImage_le {k : Type u} [CommRing k] {G : Type u} [Group G] {Δ : Type u} [Group Δ] (f : Δ →* G) {M : Rep k G} {N : Rep k Δ}
    (φ : Rep.res f M ⟶ N) (T : Subgroup G) [T.Normal] (S : Subgroup Δ) [S.Normal]
    (hST : S ≤ T.comap f) :
    (inflationImage M T).map (groupCohomology.map f φ 1).hom ≤ inflationImage N S := by sorry
