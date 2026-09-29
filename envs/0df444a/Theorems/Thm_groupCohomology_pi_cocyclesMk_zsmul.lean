-- Prove2me | Theorems.Thm_groupCohomology_pi_cocyclesMk_zsmul
-- name    : groupCohomology.pi_cocyclesMk_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/0ef01006-31bf-57e9-9574-2e7637d241f4
-- title:
--   The class of m· x is m times the class of x
-- statement:
--   Let $G$ be a group and let $A$ be a representation of $G$ over $\mathbb{Z}$, i.e. an object of `Rep ℤ G`; let $n$ be a natural number and $m$ an integer. Let $x \colon (\mathrm{Fin}\ n \to G) \to A$ be an inhomogeneous $n$-cochain, and suppose that the degree-$n$ differential of the inhomogeneous cochain complex of $A$ annihilates $x$, so that $x$ is an $n$-cocycle, and that it likewise annihilates $m \cdot x$ (this second hypothesis, although a formal consequence of the first by additivity of the differential, is taken as a separate argument so that the cocycle $m \cdot x$ can be formed). Write `cocyclesMk` for the passage from a cochain together with a proof that the differential kills it to the corresponding element of the module of $n$-cocycles, and $\pi$ for the quotient map from $n$-cocycles to $H^n(G, A)$. The assertion is that the class of $m \cdot x$ in $H^n(G, A)$ equals $m$ times the class of $x$, i.e. $\pi_{A,n}(\mathrm{cocyclesMk}(m \cdot x)) = m \cdot \pi_{A,n}(\mathrm{cocyclesMk}(x))$.
--
--   This records the $\mathbb{Z}$-linearity of the class map on cocycles, in the concrete form in which cocycles are presented by raw inhomogeneous cochains together with a vanishing hypothesis. It is used in the idelic torsion step [`NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag`](thm.html#NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag), where one must multiply an explicit cocycle by an integer and track the effect on its cohomology class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_pi_cocyclesMk_zsmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.pi_cocyclesMk_zsmul
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0) (hmx : (inhomogeneousCochains.d A n).hom (m • x) = 0) :
    groupCohomology.π A n (groupCohomology.cocyclesMk (m • x) hmx) = m • groupCohomology.π A n (groupCohomology.cocyclesMk x hx) := by sorry
