-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_for_edge_count
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:14:52.556295+00:00
-- url     : https://prove2.me/theorems/6230202c-e2d1-4f54-a7eb-9eadc154ee57
-- title:
--   Every finite planar graph extends to a triangulation for the edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges. For three vertices the extension is the triangle. The lemma includes disconnected starting graphs; it does not assume that the original graph is maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_extension_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, G ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
