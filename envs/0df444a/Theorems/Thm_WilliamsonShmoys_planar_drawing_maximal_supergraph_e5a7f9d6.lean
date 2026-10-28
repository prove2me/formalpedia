-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_e5a7f9d6
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_e5a7f9d6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:20:31.461778+00:00
-- url     : https://prove2.me/theorems/5cd7143e-6683-4779-a50f-e516bc018367
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal under inclusion among planar supergraphs. Prove this by maximizing the edge count over the finite set of simple graphs containing K that have planar drawings; any strict planar extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_e5a7f9d6
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧
        ∀ M : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L := by sorry
