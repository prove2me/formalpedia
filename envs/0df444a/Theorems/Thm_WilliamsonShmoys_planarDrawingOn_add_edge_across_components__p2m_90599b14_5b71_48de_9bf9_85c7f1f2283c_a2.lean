-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
-- name    : WilliamsonShmoys.planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:23:47.423914+00:00
-- url     : https://prove2.me/theorems/192a9465-58bd-4b48-bdb5-97f89f722a6b
-- title:
--   A drawable disconnected graph on at least three vertices admits a drawable edge extension
-- statement:
--   For a finite linearly ordered vertex type of size at least three, a drawable disconnected graph has a drawable supergraph that adds an edge between distinct nonadjacent vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hNotConnected : ¬ J.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
      ∃ K : SimpleGraph V,
        J ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
