-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_54a0e51c
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_54a0e51c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:38:29.171399+00:00
-- url     : https://prove2.me/theorems/3e1ebe34-f4e9-404f-bbfd-29950cf28199
-- title:
--   Edge-maximal planar extension on a fixed vertex set
-- statement:
--   Every graph with the specified crossing-free drawing has a drawing-preserving supergraph on the same finite ordered vertex type that is maximal among such supergraphs. Choose a drawable supergraph with the largest edge count among the finitely many simple graphs on the vertex type. The original graph ensures the candidate set is nonempty, and any strict drawable extension would contradict maximality of the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
