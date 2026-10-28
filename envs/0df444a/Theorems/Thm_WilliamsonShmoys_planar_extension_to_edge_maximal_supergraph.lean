-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal_supergraph
-- name    : WilliamsonShmoys.planar_extension_to_edge_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:11:46.823447+00:00
-- url     : https://prove2.me/theorems/a824ede2-66f8-4e1d-a8a8-b57076146409
-- title:
--   Extend a planar graph to an edge-maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_edge_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V,
      L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V, M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M := by sorry
