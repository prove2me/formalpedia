-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_of_edge_insertions
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_of_edge_insertions
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:35:09.382988+00:00
-- url     : https://prove2.me/theorems/edd61be6-58f0-4c1b-8a79-8cf61945c1a5
-- title:
--   Maximal planar extension is connected
-- statement:
--   If every disconnected planar supergraph of K has a planar supergraph with strictly more edges, then K has a connected planar supergraph whose edge count is at least that of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_of_edge_insertions {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hstep : ∀ (L : SimpleGraph V), K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → ¬ L.Connected → ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ L.edgeSet.ncard < M.edgeSet.ncard) : ∃ K' : SimpleGraph V, K ≤ K' ∧ K'.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧ K.edgeSet.ncard ≤ K'.edgeSet.ncard := by sorry
