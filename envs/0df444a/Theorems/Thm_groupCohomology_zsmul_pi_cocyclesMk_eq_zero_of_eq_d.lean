-- Prove2me | Theorems.Thm_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d
-- name    : groupCohomology.zsmul_pi_cocyclesMk_eq_zero_of_eq_d
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/b139fd57-fc9f-5c1a-b95c-ce74e96888ea
-- title:
--   Integer multiple of a cocycle class vanishes if it is a coboundary
-- statement:
--   Let $G$ be a group (in the lowest universe), let $A$ be a $\mathbb{Z}$-linear representation of $G$ in `Rep.{0} ℤ G`, let $n$ be a natural number and $m$ an integer. Let $x\colon (\mathrm{Fin}(n+1)\to G)\to A$ be an inhomogeneous $(n+1)$-cochain which is a cocycle, i.e. the differential `inhomogeneousCochains.d A (n + 1)` of the inhomogeneous cochain complex of $A$ sends $x$ to $0$, and let $y\colon (\mathrm{Fin}\,n\to G)\to A$ be an $n$-cochain such that $m\cdot x$ equals the image of $y$ under the differential `inhomogeneousCochains.d A n`. The conclusion is that $m$ times the cohomology class of $x$ vanishes: with `groupCohomology.cocyclesMk x hx` the element of the module of $(n+1)$-cocycles determined by $x$ and its cocycle condition, and `groupCohomology.π A (n + 1)` the canonical map from cocycles to $H^{n+1}(G,A)$, one has $m \cdot \pi(\,[x]_{\mathrm{cocyc}}\,) = 0$ in $H^{n+1}(G,A)$.
--
--   This is the standard fact that a cochain whose $m$-th multiple is a coboundary has $m$-torsion cohomology class, stated in the concrete spelling by which a cocycle is presented as a function on tuples of group elements together with its cocycle identity. It is used in the level-arithmetic part of the argument, where a divisibility relation between an explicit cochain and a coboundary is converted into the vanishing of an integer multiple of a class in $H^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.zsmul_pi_cocyclesMk_eq_zero_of_eq_d
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin (n + 1) → G) → A)
    (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0) (y : (Fin n → G) → A)
    (h : m • x = (inhomogeneousCochains.d A n).hom y) :
    m • groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = 0 := by sorry
