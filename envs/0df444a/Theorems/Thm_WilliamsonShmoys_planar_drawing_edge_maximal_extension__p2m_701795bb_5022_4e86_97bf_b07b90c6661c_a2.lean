-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:01.259398+00:00
-- url     : https://prove2.me/theorems/65bb11c9-29c3-416d-befd-00639d3c1860
-- title:
--   Extend a planar drawing to an edge-maximal planar graph
-- statement:
--   Every finite graph with a planar drawing is contained in an inclusion-maximal planar graph on the same vertex type, and the extension has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    [DecidableRel P.Adj] :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) ∧
      (∀ [DecidableRel H.Adj], P.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
