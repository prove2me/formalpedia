-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:46:02.359663+00:00
-- url     : https://prove2.me/theorems/6a3672e5-8625-4230-b81a-48a51d366765
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. Choose a drawable supergraph with the greatest number of edges from the finite family of edge subsets; any strict drawable extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
