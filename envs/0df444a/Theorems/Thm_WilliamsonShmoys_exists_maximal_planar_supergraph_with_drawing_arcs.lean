-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_with_drawing_arcs
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_with_drawing_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:13:19.746464+00:00
-- url     : https://prove2.me/theorems/29a3dbf5-7904-4828-8a95-bd7678bc000b
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal under graph inclusion. Choose a drawable supergraph of K with the largest edge count; any drawable strict extension would have more edges. This removes the finite maximality choice from the parent. The independent proof route is to use finiteness of the set of simple graphs on V and strict monotonicity of edge-set cardinality. This child does not require the lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_with_drawing_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  sorry
