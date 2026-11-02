-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:41.173207+00:00
-- url     : https://prove2.me/theorems/61f827a4-90a1-438d-8856-22a36ff94a2a
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A graph on at least three vertices that has the stated planar drawing and is maximal among planar supergraphs has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
