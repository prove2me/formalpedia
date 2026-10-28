-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:56:49.803722+00:00
-- url     : https://prove2.me/theorems/b1854fdb-fd2a-4adc-a8a5-dfb1cdfc2f81
-- title:
--   Connected supergraph preserving a planar drawing
-- statement:
--   A drawable graph on at least three vertices has a connected drawable supergraph on the same vertices whose edge count is at least as large.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Q.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
