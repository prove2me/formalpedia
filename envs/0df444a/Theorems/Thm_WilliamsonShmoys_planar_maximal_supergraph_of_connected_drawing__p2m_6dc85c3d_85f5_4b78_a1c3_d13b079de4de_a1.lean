-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:05.799403+00:00
-- url     : https://prove2.me/theorems/90a1d3cf-69db-4650-95dd-fb78166e4c20
-- title:
--   Maximal drawable supergraph of a connected planar graph
-- statement:
--   Extend the given connected graph to an inclusion-maximal graph on the same vertices that still has the specified crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hconn : M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) := by sorry
