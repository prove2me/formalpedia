-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2
-- name    : WilliamsonShmoys.planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:49.061587+00:00
-- url     : https://prove2.me/theorems/e87f3d6d-f5ac-4caa-95af-19e806d71ee4
-- title:
--   A planar graph has a connected planar supergraph
-- statement:
--   Every nonempty finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex type. The finite connected components can be redrawn in separate regions and joined by noncrossing arcs; if the graph is already connected, take the graph itself.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hne : Nonempty V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ (∀ x y, N.Reachable x y) ∧ HasPlanarDrawingOn N := by sorry
