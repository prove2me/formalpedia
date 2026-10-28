-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:45:04.766735+00:00
-- url     : https://prove2.me/theorems/fb358d66-00e7-4873-ac9b-d2a4a040c855
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertex type. The finite maximization argument needs no lower bound on the vertex count: choose a drawable supergraph of K with maximum edge-set cardinality; a strict drawable enlargement would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      ∀ M : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeSet ⊆ M.edgeSet → L.edgeSet = M.edgeSet := by sorry
