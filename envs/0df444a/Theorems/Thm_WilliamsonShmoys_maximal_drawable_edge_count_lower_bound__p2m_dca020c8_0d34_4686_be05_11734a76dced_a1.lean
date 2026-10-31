-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:44.250324+00:00
-- url     : https://prove2.me/theorems/9d48574e-becf-4744-b845-090de246cf6f
-- title:
--   Maximality forces the planar edge-count lower bound
-- statement:
--   A drawable graph that is maximal under drawable supergraphs, with at least three vertices, has at least 3n−6 edges. In a planar embedding, maximality forces every face to be triangular; Euler’s formula then yields the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard := by sorry
