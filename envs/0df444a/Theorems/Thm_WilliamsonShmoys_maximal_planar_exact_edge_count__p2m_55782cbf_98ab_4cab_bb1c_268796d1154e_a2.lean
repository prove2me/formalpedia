-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:06:44.238996+00:00
-- url     : https://prove2.me/theorems/fa30b313-3ade-47b7-9dcc-bae00c9eb7a0
-- title:
--   Exact edge count for edge-maximal planar graphs
-- statement:
--   For a finite ordered vertex type with at least three vertices, an edge-maximal simple graph admitting the supplied crossing-free drawing has exactly 3n − 6 edges. The lower boundary n = 3 gives three edges, as expected; the statement retains the target’s vertex-count and maximality hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M.edgeSet <= N.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N.edgeSet = M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
