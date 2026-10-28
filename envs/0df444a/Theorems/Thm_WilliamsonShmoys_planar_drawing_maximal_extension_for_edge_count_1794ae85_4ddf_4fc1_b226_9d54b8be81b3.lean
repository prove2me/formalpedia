-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:12:32.541967+00:00
-- url     : https://prove2.me/theorems/ac57a375-e894-4e97-b534-9e82dfe3bac2
-- title:
--   Edge-maximal drawable extension on a finite vertex type
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
