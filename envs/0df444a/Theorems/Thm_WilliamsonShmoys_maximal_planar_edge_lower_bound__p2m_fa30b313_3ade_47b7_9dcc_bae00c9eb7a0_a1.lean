-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:42:55.18872+00:00
-- url     : https://prove2.me/theorems/6162c15f-6fba-4097-b3f1-9407bb3035c9
-- title:
--   Edge lower bound for an edge-maximal planar drawing
-- statement:
--   An edge-maximal graph with the supplied planar drawing and at least three vertices has at least 3n − 6 edges. The proof route is to use maximality to establish connectedness and triangular face boundaries, then apply Euler’s formula. The statement preserves the parent’s full drawing and maximality hypotheses, including the n = 3 case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M.edgeSet <= N.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N.edgeSet = M.edgeSet) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
