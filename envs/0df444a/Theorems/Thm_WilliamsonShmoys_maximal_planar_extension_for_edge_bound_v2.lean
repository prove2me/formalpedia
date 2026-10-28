-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_for_edge_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_extension_for_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:55:17.466263+00:00
-- url     : https://prove2.me/theorems/070b12f2-3b8e-46e0-b4cb-774544eb4d2d
-- title:
--   Maximal planar extension for the edge bound
-- statement:
--   A connected graph with at least three vertices and a planar drawing has a connected, inclusion-maximal planar supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_for_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard <= H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V, H < H' → ¬ WilliamsonShmoys.HasPlanarDrawingOn H' := by sorry
