-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_maximal_extension_e9c82dc3
-- name    : WilliamsonShmoys.finite_drawable_supergraph_maximal_extension_e9c82dc3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:20:37.934992+00:00
-- url     : https://prove2.me/theorems/dfd03c37-ceb9-467f-9435-c1f34ded467e
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph that is maximal among drawable supergraphs and has at least as many edges. Choose a drawable supergraph containing M with maximum edge count among the finitely many simple graphs on V. A drawable supergraph of that choice cannot have strictly more edges, so it equals the choice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_supergraph_maximal_extension_e9c82dc3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
