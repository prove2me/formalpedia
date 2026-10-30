-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_a8cccb55
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_a8cccb55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:18:14.38459+00:00
-- url     : https://prove2.me/theorems/a1fa2dac-1a64-49e2-b5b3-0bb37fb735e5
-- title:
--   Connected planar augmentation of a drawn graph
-- statement:
--   A finite drawable graph with at least three vertices has a connected drawable supergraph on the same vertices and with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_a8cccb55
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      (W.edgeSet.ncard ≤ H.edgeSet.ncard ∧
       H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by sorry
