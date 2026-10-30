-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_maximal_edge_count_54a0e51c
-- name    : WilliamsonShmoys.planar_triangulation_extension_for_maximal_edge_count_54a0e51c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:12:24.399765+00:00
-- url     : https://prove2.me/theorems/9ae943a3-ed40-4a04-9abb-0ed7e0a1d12e
-- title:
--   Triangulated planar extension with maximal edge count
-- statement:
--   Any graph with the supplied crossing-free drawing predicate and at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_for_maximal_edge_count_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
