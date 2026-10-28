-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_edge_maximal_extension_3e41a808
-- name    : WilliamsonShmoys.exists_planar_drawing_edge_maximal_extension_3e41a808
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:20:08.766608+00:00
-- url     : https://prove2.me/theorems/d795819c-3dd5-4eaa-8770-5ccbad7bc20d
-- title:
--   A finite drawable graph has an edge-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. Choose a drawable supergraph with the greatest number of edges; finiteness supplies such a choice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_drawing_edge_maximal_extension_3e41a808
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun H : SimpleGraph V =>
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → H = K := by sorry
