-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulation_extension_3daebd93
-- name    : WilliamsonShmoys.planar_drawing_edge_count_triangulation_extension_3daebd93
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:03:41.988673+00:00
-- url     : https://prove2.me/theorems/155d6882-ad2a-454e-b023-0be22a3f79b8
-- title:
--   Triangulation extension and edge count for a finite planar drawing
-- statement:
--   Every finite drawable simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly $3|V|-6$ edges. The parent applies maximality to this supergraph, so it equals the original graph and yields the target bound. At three vertices the extension is $K_3$; the proof must also join disconnected components before triangulating.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_triangulation_extension_3daebd93
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
