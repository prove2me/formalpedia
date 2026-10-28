-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_cardinality_planar_supergraph
-- name    : WilliamsonShmoys.exists_max_cardinality_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:07:10.194156+00:00
-- url     : https://prove2.me/theorems/b5c55fa6-15f3-446f-8959-a0ce6dc820b3
-- title:
--   A maximum planar supergraph exists
-- statement:
--   Among the planar supergraphs of a given planar graph on a finite vertex type, there is one with maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_cardinality_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, N ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  sorry
