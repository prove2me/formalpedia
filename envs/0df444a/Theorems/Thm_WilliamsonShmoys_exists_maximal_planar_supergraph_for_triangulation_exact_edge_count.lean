-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_triangulation_exact_edge_count
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:56:29.790771+00:00
-- url     : https://prove2.me/theorems/2d60016c-11f8-47b9-8704-3b12f56def78
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in an inclusion-maximal drawable graph on the same vertex type. This removes the finite maximization step from the parent. Prove it by maximizing edge-set cardinality over the finite family of drawable supergraphs containing M; a proper drawable extension would have more edges. The claim also applies when the vertex count is below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_exact_edge_count {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by sorry
