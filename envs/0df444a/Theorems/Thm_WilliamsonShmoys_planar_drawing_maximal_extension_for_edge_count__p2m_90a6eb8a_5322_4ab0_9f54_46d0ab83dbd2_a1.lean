-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:04.301283+00:00
-- url     : https://prove2.me/theorems/4f8ddee9-6bbc-42a8-909b-77c7ff633307
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. This is obtained by choosing a drawable supergraph with the largest edge count from the finite set of simple graphs on the vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ L := by sorry
