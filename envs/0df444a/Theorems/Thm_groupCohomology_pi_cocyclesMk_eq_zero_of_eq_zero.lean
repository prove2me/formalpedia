-- Prove2me | Theorems.Thm_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero
-- name    : groupCohomology.pi_cocyclesMk_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/8a2b2f9f-9a8f-5f7e-88df-26653433e5a4
-- title:
--   The cohomology class of the zero cochain vanishes
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $A$ be a representation of $G$ over $k$ (an object of `Rep k G`, in the zeroth universe), and let $n$ be a natural number. Let $x \colon (\mathrm{Fin}\ n \to G) \to A$ be an inhomogeneous $n$-cochain, i.e. a function of $n$ group variables with values in the underlying module of $A$, and suppose that $x$ is a cocycle: the differential `inhomogeneousCochains.d A n` of the inhomogeneous cochain complex, applied to $x$, is the zero $(n+1)$-cochain. Suppose furthermore that $x$ itself is the zero cochain. Then the image of $x$ under the canonical map to cohomology vanishes: the element `groupCohomology.cocyclesMk x hx` of the module of $n$-cocycles of $A$, obtained from $x$ together with the proof `hx` of the cocycle condition, is sent by the projection $\pi_{A,n}$ from cocycles to $H^n(G,A)$ to $0$. The point of the statement is the dependent shape: the cocycle witness `hx` refers to $x$, whereas the vanishing of $x$ is a separate propositional hypothesis.
--
--   This records the obvious fact that the class in $H^n(G,A)$ represented by the zero inhomogeneous $n$-cochain is zero, in the form needed when the vanishing of a cochain is only available as a propositional equality. It is used in the $S$-idele level computations, namely in [`NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag`](thm.html#NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag) and [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp), to discard coordinates that are known to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.pi_cocyclesMk_eq_zero_of_eq_zero
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0) (h0 : x = 0) :
    groupCohomology.π A n (groupCohomology.cocyclesMk x hx) = 0 := by sorry
