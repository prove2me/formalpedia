-- Prove2me | Theorems.Thm_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map
-- name    : groupCohomology.Cores.map_subtype_cores_eq_finsum_cores_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a4c8874e-5dab-52d7-b953-825d75220653
-- title:
--   Double coset formula for the degree-2 corestriction
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group and $A$ a $k$-linear representation of $G$; let $H, D \le G$ be subgroups. A `Cores.Transversal H` is a normalised section of the left cosets: a map $\sigma \colon G/H \to G$ with $\sigma(q) \in q$ for all $q$ and $\sigma(H) = 1$; let $\tau$ be such a transversal for $H$, and let $\mathrm{cores}$ denote the resulting degree-$2$ transfer $H^2(H, A|_H) \to H^2(G, A)$, obtained from the cochain-level corestriction attached to $\tau$ by passage to cohomology. Let $\iota$ be a finite type and $g \colon \iota \to G$ a family such that $i \mapsto D g_i H$ is a bijection of $\iota$ onto the double coset space $D \backslash G / H$, and assume $g_{i_0} = 1$ for some $i_0$. For each $i$ write $K_i \le D$ for the subgroup of $D$ with underlying set $D \cap g_i H g_i^{-1}$ (the subgroup `(MulAut.conj (g i) • H).subgroupOf D`), and suppose given: a normalised transversal $\tau_{D,i}$ of $K_i$ in $D$; a group homomorphism $c_i \colon K_i \to H$ with $c_i(x) = g_i^{-1} x g_i$ in $G$; and a morphism $T_i$ of representations of $K_i$ from $A|_H$ restricted along $c_i$ to $A|_D$ restricted along the inclusion $K_i \le D$, whose underlying map is $a \mapsto \rho_A(g_i)\,a$. Then for every $y \in H^2(H, A|_H)$, the restriction of $\mathrm{cores}_\tau(y)$ along the inclusion $D \le G$ (with the identity coefficient map on $A|_D$) equals the finite sum over $i \in \iota$ of the transfers $\mathrm{cores}_{\tau_{D,i}}$ from $K_i$ to $D$ of the images of $y$ under the degree-$2$ cohomology maps induced by $(c_i, T_i)$.
--
--   This is the double coset (Mackey) formula expressing the restriction to $D$ of a corestriction from $H$ as a sum of corestrictions over the double cosets $D \backslash G / H$, here in degree $2$ and with the transfer normalised through an explicit transversal. It is used in the computation of Herbrand quotients, in the reduction of sums of corestrictions over a family of subgroups to sums over intersections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map.lean

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology
open scoped Pointwise

theorem groupCohomology.Cores.map_subtype_cores_eq_finsum_cores_map
    {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G)
    (H D : Subgroup G) (τ : Cores.Transversal H)

    {ι : Type} [Finite ι] (g : ι → G)
    (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i))
    (hone : ∃ i₀, g i₀ = 1)

    (τD : ∀ i, Cores.Transversal ((MulAut.conj (g i) • H).subgroupOf D))
    (c : ∀ i, ↥((MulAut.conj (g i) • H).subgroupOf D) →* ↥H)
    (hc : ∀ i (x : ↥((MulAut.conj (g i) • H).subgroupOf D)), ((c i x : ↥H) : G) = (g i)⁻¹ * ((x : ↥D) : G) * g i)
    (T : ∀ i, Rep.res (c i) (Rep.res H.subtype A) ⟶ Rep.res ((MulAut.conj (g i) • H).subgroupOf D).subtype (Rep.res D.subtype A))
    (hT : ∀ i (a : A), (T i).hom a = A.ρ (g i) a)
    (y : groupCohomology (Rep.res H.subtype A) 2) :
    (groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype A)) 2).hom (Cores.cores A τ y) =
      ∑ᶠ i, Cores.cores (Rep.res D.subtype A) (τD i) ((groupCohomology.map (c i) (T i) 2).hom y) := by sorry
