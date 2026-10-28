-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_20261027_job59ad8832
-- name    : WilliamsonShmoys.maximal_planar_extension_20261027_job59ad8832
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:38:19.923972+00:00
-- url     : https://prove2.me/theorems/009bf745-9075-4d43-a242-26d9140b6317
-- title:
--   Every drawable graph has a maximal drawable extension
-- statement:
--   Any drawable graph on a finite vertex type has a drawable supergraph on that same type to which no edge can be added while preserving drawability. There are only finitely many simple graphs on the type, and the input graph supplies a nonempty set of drawable supergraphs; maximize edge-set cardinality within that set. This step does not require connectedness and applies without a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_20261027_job59ad8832
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
