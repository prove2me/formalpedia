-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:42:03.312442+00:00
-- url     : https://prove2.me/theorems/691a5387-ed7b-4166-8549-c5387ceade06
-- title:
--   Add a planar bridge between distinct components
-- statement:
--   Given a planar drawing of a disconnected graph on at least three vertices, there is a strictly larger planar supergraph containing an edge between vertices that were in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v ∧
      ∃ H : SimpleGraph V, K < H ∧
        WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Adj u v := by sorry
