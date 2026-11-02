-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:32.652197+00:00
-- url     : https://prove2.me/theorems/d6b9112d-6e11-42e8-8b1b-3d46cf1b698c
-- title:
--   Planar supergraph with the maximal planar edge lower bound
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least 3n − 6 edges. This isolates constructing a triangulated extension and obtaining its edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
