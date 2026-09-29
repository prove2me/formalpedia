-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
-- name    : groupCohomology.exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/93d84a40-e630-58c6-924e-21dcf1a3d633
-- title:
--   Vanishing of H¹(G,ℤ[X]) for a permutation module
-- statement:
--   Let $G$ be a finite group acting on a type $X$, and let $X \to_{f} \mathbb{Z}$ denote the finitely supported functions $X \to \mathbb{Z}$, i.e. the permutation module $\mathbb{Z}[X]$, on which $G$ acts by pushing the support forward along $g$: the element $g$ sends $\varphi$ to $\mathrm{Finsupp.mapDomain}\,(g \bullet -)\,\varphi$, the function $x \mapsto \varphi(g^{-1}x)$. Let $n \colon G \to (X \to_{f} \mathbb{Z})$ be any function satisfying the inhomogeneous $1$-cocycle identity $n(gh) = n(g) + \mathrm{Finsupp.mapDomain}\,(g \bullet -)\,(n(h))$ for all $g, h \in G$. The assertion is that $n$ is a coboundary of the indicated shape: there exists a finitely supported $m \colon X \to \mathbb{Z}$ such that for every $g \in G$ one has $n(g) = m - \mathrm{Finsupp.mapDomain}\,(g \bullet -)\,m$, i.e. $n(g)(x) = m(x) - m(g^{-1}x)$ for all $x$. No hypothesis is placed on $X$ beyond the $G$-action, and finiteness is assumed of $G$ only.
--
--   This is the vanishing of the first cohomology group $H^1(G,\mathbb{Z}[X])$ of a finite group acting on a permutation module over $\mathbb{Z}$, stated in explicit cocycle–coboundary form. It is used in the adelic part of the development, in [`NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem`](thm.html#NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem), where $X$ is a $G$-stable set of finite places and $\mathbb{Z}[X]$ records valuations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem groupCohomology.exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (n : G → X →₀ ℤ) (hn : ∀ g h : G, n (g * h) = n g + Finsupp.mapDomain (g • ·) (n h)) :
    ∃ m : X →₀ ℤ, ∀ g : G, n g = m - Finsupp.mapDomain (g • ·) m := by sorry
