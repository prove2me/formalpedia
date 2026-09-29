-- Prove2me | Theorems.Thm_groupCohomology_Cores_corFin_d
-- name    : groupCohomology.Cores.corFin_d
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c939e4c8-c33c-5bf1-8b23-1a5a28c5e62d
-- title:
--   Corestriction cochains commute with the inhomogeneous differential
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a representation of $G$ over $k$, and $H \le G$ a subgroup of finite index. Let $\tau$ be a transversal for $H$, i.e. a section $\sigma \colon G/H \to G$ of the quotient map (so $\sigma(q)H = q$ for all $q$) which is normalised by $\sigma(H) = 1$. Fix $n \in \mathbb{N}$ and an inhomogeneous $n$-cochain $u \colon (\mathrm{Fin}\ n \to H) \to A$ for $H$ with values in the restricted representation. The corestriction operator `corFin` sends such a $u$ to the $n$-cochain of $G$ given by
--   $$(\mathrm{cor}_n u)(g) \;=\; \sum_{q \in G/H} \rho_A(\sigma(q))\, u\Big(i \mapsto \lambda\big(\sigma(q)^{-1} P_i(g)\big)^{-1}\,\lambda\big(\sigma(q)^{-1} P_{i+1}(g)\big)\Big),$$
--   where $P_m(g)$ denotes the partial products `Fin.partialProd` of $g \colon \mathrm{Fin}\ n \to G$ and $\lambda$ is the $H$-valued map `Transversal.lam` attached to $\tau$. The assertion is the equality of $(n+1)$-cochains of $G$
--   $$\mathrm{cor}_{n+1}\big(d^n u\big) \;=\; d^n\big(\mathrm{cor}_n u\big),$$
--   where on the left $d^n$ is the degree-$n$ differential of Mathlib's `inhomogeneousCochains` of $\mathrm{Res}^G_H A$ and on the right that of `inhomogeneousCochains` of $A$. No cocycle condition on $u$ is assumed.
--
--   This is the statement that the Eckmann transfer (corestriction), defined on $\mathrm{Fin}$-indexed inhomogeneous cochains by averaging over a normalised transversal, is a map of cochain complexes, and hence induces corestriction maps $H^n(H,A) \to H^n(G,A)$. It is used in the level arithmetic of the argument, where a cochain whose restriction to a finite-index subgroup is a coboundary is transferred back up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Cores_corFin_d.lean

import Mathlib
import Definitions.Def_GroupCohomology_CorestrictionFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology groupCohomology.Cores

theorem groupCohomology.Cores.corFin_d
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ : Transversal H) (n : ℕ) (u : (Fin n → H) → A) :
    corFin A τ (n + 1) (((inhomogeneousCochains (Rep.res H.subtype A)).d n (n + 1)).hom u)
      = ((inhomogeneousCochains A).d n (n + 1)).hom (corFin A τ n u) := by sorry
