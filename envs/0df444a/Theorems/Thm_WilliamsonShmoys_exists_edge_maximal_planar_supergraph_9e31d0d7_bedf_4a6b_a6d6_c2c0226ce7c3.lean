-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:13:43.19928+00:00
-- url     : https://prove2.me/theorems/51c6bfa8-0572-4209-ba6e-1c622d52aaf3
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal under edge inclusion. The extension has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    exists T : SimpleGraph V,
      (forall u v, S.Adj u v -> T.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn T /\
      S.edgeSet.ncard <= T.edgeSet.ncard /\
      (forall R : SimpleGraph V,
        (forall u v, T.Adj u v -> R.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn R -> R = T) := by sorry
