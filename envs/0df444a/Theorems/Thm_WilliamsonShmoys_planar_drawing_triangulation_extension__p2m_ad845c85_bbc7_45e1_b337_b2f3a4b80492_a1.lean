-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:44.448571+00:00
-- url     : https://prove2.me/theorems/b1b3c510-149d-42bd-a072-8549c5a8211b
-- title:
--   Triangulation extension on the same vertex set
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. Applying maximality to this extension gives the target’s lower bound. A proof route is to extend by drawable edges to a maximal supergraph, then prove that such an embedding is connected and every face is triangular; disconnected drawings and the three-vertex case need explicit treatment.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
