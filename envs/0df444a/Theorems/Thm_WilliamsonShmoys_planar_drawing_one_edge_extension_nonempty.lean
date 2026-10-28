-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_extension_nonempty
-- name    : WilliamsonShmoys.planar_drawing_one_edge_extension_nonempty
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:09:09.201669+00:00
-- url     : https://prove2.me/theorems/c33cfb39-e486-4c94-aa63-3ed42e529fb6
-- title:
--   Add a planar bridge between disconnected vertices on a nontrivial vertex type
-- statement:
--   For a finite planar drawing on at least three vertices, if the graph is disconnected, it has a planar supergraph with an edge joining vertices that were in different connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_one_edge_extension_nonempty
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v := by sorry
