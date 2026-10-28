-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:04:40.292899+00:00
-- url     : https://prove2.me/theorems/77fbf7e8-704b-4322-bfc5-8a041428bfea
-- title:
--   Maximal drawable supergraph for edge counting
-- statement:
--   A finite drawable graph has an inclusion-maximal drawable supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ H' : SimpleGraph V,
        H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
