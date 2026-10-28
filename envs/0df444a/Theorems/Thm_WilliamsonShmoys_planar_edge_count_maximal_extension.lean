-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_extension
-- name    : WilliamsonShmoys.planar_edge_count_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:49:10.230083+00:00
-- url     : https://prove2.me/theorems/4f63021f-2831-4126-aacf-1059cbfa7e5d
-- title:
--   Extend a planar graph to an edge-maximal planar supergraph
-- statement:
--   Every planar drawing on a finite ordered vertex type with at least three vertices extends, without changing the vertex type, to a drawing of a graph that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H <= K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
