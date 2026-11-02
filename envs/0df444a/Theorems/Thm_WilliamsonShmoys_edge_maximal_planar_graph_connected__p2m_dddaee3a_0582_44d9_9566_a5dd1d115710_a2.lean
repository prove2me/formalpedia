-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:43.855009+00:00
-- url     : https://prove2.me/theorems/028b57dc-ebab-41ef-892a-6b94678daa69
-- title:
--   An edge-maximal drawable graph is connected
-- statement:
--   A drawable graph on at least three vertices that admits no drawable strict supergraph on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ H : SimpleGraph V,
      M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M) :
    M.Connected := by sorry
