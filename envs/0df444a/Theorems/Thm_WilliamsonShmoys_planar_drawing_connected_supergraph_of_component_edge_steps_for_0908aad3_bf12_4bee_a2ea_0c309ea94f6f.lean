-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:02:42.831813+00:00
-- url     : https://prove2.me/theorems/d5d39e2d-c5cf-4d40-96df-99aecbdafec7
-- title:
--   Iterate component-joining edge steps
-- statement:
--   For a nonempty finite vertex type, if every drawable disconnected graph admits a drawable supergraph with an edge joining two of its components, then the initial graph has a connected drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G)
    (hV : 0 < Fintype.card V)
    (hstep : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
