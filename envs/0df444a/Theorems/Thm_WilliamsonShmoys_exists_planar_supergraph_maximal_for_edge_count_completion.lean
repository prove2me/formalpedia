-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_edge_count_completion
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal_for_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:42:12.945992+00:00
-- url     : https://prove2.me/theorems/5fa5e5e8-1962-41d3-a8f9-fa4624c281b1
-- title:
--   Existence of a maximal planar supergraph for edge-count completion
-- statement:
--   Every planar graph on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal among planar supergraphs under edge inclusion. Finiteness and the input drawing make the finite maximization argument possible; no minimum size assumption is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal_for_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
