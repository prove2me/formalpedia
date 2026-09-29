-- Prove2me | Theorems.Thm_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq
-- name    : groupCohomology.exists_eq_add_d_of_pi_cocyclesMk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/058b7f73-68a5-5d42-a855-42ac9817b22c
-- title:
--   Equal cohomology classes differ by a coboundary of cochains
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a $k$-linear representation of $G$ (an object of `Rep k G`), and let $n$ be a natural number. Let $x, x' : (\mathrm{Fin}(n+1) \to G) \to A$ be two inhomogeneous $(n+1)$-cochains, i.e. functions of $n+1$ group variables with values in the underlying module of $A$, each annihilated by the differential out of degree $n+1$: the hypotheses are that the linear map underlying `inhomogeneousCochains.d A (n + 1)` sends $x$ to $0$ and likewise sends $x'$ to $0$, so that both are $(n+1)$-cocycles. Assume furthermore that the two cocycles they determine, obtained via `groupCohomology.cocyclesMk`, have the same image under the canonical projection `groupCohomology.π A (n + 1)` from cocycles in degree $n+1$ to $H^{n+1}(G, A)$. The conclusion is that there exists an inhomogeneous $n$-cochain $y : (\mathrm{Fin}\,n \to G) \to A$ with $x = x' + d y$, where $dy$ is the value at $y$ of the linear map underlying `inhomogeneousCochains.d A n`. Thus equality of cohomology classes is witnessed by an explicit identity of raw functions on tuples of group elements.
--
--   This is the statement that $H^{n+1}(G,A)$ is cocycles modulo coboundaries, in the concrete spelling by functions on $(n+1)$-tuples of group elements: two cocycles with the same class differ by the differential of an explicit $n$-cochain. It is used in the computations with $S$-idele cochains, where an equality of cohomology classes must be converted into a cochain-level identity, as in [`NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag`](thm.html#NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag) and [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_eq_add_d_of_pi_cocyclesMk_eq
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (x x' : (Fin (n + 1) → G) → A)
    (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0) (hx' : (inhomogeneousCochains.d A (n + 1)).hom x' = 0)
    (h : groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x' hx')) :
    ∃ y : (Fin n → G) → A, x = x' + (inhomogeneousCochains.d A n).hom y := by sorry
