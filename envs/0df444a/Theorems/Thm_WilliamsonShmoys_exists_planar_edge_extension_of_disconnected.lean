-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_extension_of_disconnected
-- name    : WilliamsonShmoys.exists_planar_edge_extension_of_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:15:20.266009+00:00
-- url     : https://prove2.me/theorems/5f1668d5-9d5b-451e-aadf-a9bde2f25f36
-- title:
--   Planar extension joining two components
-- statement:
--   A disconnected planar graph on at least three vertices has a planar supergraph that adds an edge between two vertices from different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_edge_extension_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v := by sorry
