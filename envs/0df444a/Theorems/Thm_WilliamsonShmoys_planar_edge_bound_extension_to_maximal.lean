-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_extension_to_maximal
-- name    : WilliamsonShmoys.planar_edge_bound_extension_to_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:04:17.83298+00:00
-- url     : https://prove2.me/theorems/d1ca9b26-73a7-4320-82a9-c89113a2f62c
-- title:
--   Extend a planar graph to a maximal planar supergraph
-- statement:
--   On a fixed finite vertex type, extend a graph with a planar drawing to a planar supergraph maximal under inclusion, without reducing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_extension_to_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
