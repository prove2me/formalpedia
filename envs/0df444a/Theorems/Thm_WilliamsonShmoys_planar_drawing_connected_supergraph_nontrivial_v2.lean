-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_nontrivial_v2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_nontrivial_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:51:28.979751+00:00
-- url     : https://prove2.me/theorems/1d3a19c4-ab3d-4bf8-8c18-55db824eec12
-- title:
--   Connected drawable supergraph when the vertex type is nontrivial
-- statement:
--   A drawable finite simple graph on at least three vertices is a subgraph of a connected drawable graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_nontrivial_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, W ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
