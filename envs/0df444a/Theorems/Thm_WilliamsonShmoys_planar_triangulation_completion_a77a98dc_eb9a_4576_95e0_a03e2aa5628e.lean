-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_a77a98dc_eb9a_4576_95e0_a03e2aa5628e
-- name    : WilliamsonShmoys.planar_triangulation_completion_a77a98dc_eb9a_4576_95e0_a03e2aa5628e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:36:53.329214+00:00
-- url     : https://prove2.me/theorems/b9acd79e-313f-4402-9a60-c6d0be0742ad
-- title:
--   Completion of a planar drawing to a triangulation
-- statement:
--   A finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This removes the geometric augmentation and planar edge-counting work from the parent. A proof route is to connect components with noncrossing arcs, add diagonals to nontriangular faces, and count incidences using Euler's formula; when |V| = 3, the completion is K₃. This is a substantive remaining obligation, not a proved source declaration.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_a77a98dc_eb9a_4576_95e0_a03e2aa5628e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        3 * Fintype.card V - 6 = T.edgeSet.ncard := by sorry
