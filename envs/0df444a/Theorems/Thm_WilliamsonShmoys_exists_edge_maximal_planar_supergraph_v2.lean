-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_v2
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:25:38.545899+00:00
-- url     : https://prove2.me/theorems/fdd82883-78de-4835-bd44-3c3e97b8e567
-- title:
--   Extend a drawable graph to an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that has no strictly larger drawable supergraph. This isolates the finite maximal-extension argument while retaining the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by sorry
