-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:05.593195+00:00
-- url     : https://prove2.me/theorems/7ab49c04-c8f8-4fad-ab63-3727e8925059
-- title:
--   Edge count of a maximal simple planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3n − 6 edges. The proof route is to establish that maximality makes the embedding a triangulation, apply Euler’s formula, and count edge-face incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall K : SimpleGraph V, G <= K -> HasPlanarDrawingOn K -> K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
