-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawable_graph_connected
-- name    : WilliamsonShmoys.maximal_planar_drawable_graph_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:15:14.81177+00:00
-- url     : https://prove2.me/theorems/9846273c-8e44-419b-9185-2587bb44d19a
-- title:
--   Maximal drawable graphs are connected with at least three vertices
-- statement:
--   A drawable graph on at least three vertices that is maximal by edge count among its drawable supergraphs on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawable_graph_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard)
    (hCard : 3 ≤ Fintype.card V) :
    H.Connected := by sorry
