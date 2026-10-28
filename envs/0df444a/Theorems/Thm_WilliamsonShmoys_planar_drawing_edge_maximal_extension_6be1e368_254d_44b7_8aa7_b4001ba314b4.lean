-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_6be1e368_254d_44b7_8aa7_b4001ba314b4
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension_6be1e368_254d_44b7_8aa7_b4001ba314b4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:17:42.64199+00:00
-- url     : https://prove2.me/theorems/2f424e76-4d67-44e1-a3d8-a4aacfe0edd6
-- title:
--   Extend a planar drawing to an edge-maximal supergraph
-- statement:
--   Any graph with the supplied planar drawing has a drawable supergraph on the same vertices that is maximal under drawable supergraphs and has at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension_6be1e368_254d_44b7_8aa7_b4001ba314b4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
