-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:22.659377+00:00
-- url     : https://prove2.me/theorems/162d43c0-0ffc-4e97-9a3b-e80d1c26e109
-- title:
--   Maximal planar graphs have the Euler edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → HasPlanarDrawingOn R → R = Q) (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
