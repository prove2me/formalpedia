-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_triangulation__p2m_2a979728_50d2_4a09_b4b8_e239f7e565fc_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_triangulation__p2m_2a979728_50d2_4a09_b4b8_e239f7e565fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:07.270038+00:00
-- url     : https://prove2.me/theorems/a50ae595-8ab2-4824-8fea-00e5def29cc2
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every graph drawable under the supplied crossing-free arc definition, on a finite linearly ordered vertex type with at least three vertices, is a subgraph of a drawable graph on the same vertex type having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_triangulation__p2m_2a979728_50d2_4a09_b4b8_e239f7e565fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
