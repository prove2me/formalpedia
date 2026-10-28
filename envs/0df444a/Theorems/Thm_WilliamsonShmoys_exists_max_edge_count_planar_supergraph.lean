-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_planar_supergraph
-- name    : WilliamsonShmoys.exists_max_edge_count_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:37:15.063189+00:00
-- url     : https://prove2.me/theorems/4305a1c4-bda0-48df-a772-5420541b7b89
-- title:
--   A planar supergraph with maximum edge count
-- statement:
--   Every planar graph K on a finite linearly ordered vertex type has a planar supergraph H on the same vertices whose edge count is at least that of every planar supergraph J of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_max_edge_count_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet →
        J.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
