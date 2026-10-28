-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_bridge_insertion_of_disconnected
-- name    : WilliamsonShmoys.exists_planar_bridge_insertion_of_disconnected
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T05:23:20.208357+00:00
-- url     : https://prove2.me/theorems/e04ec262-c798-48b3-8322-a983ffcd648b
-- title:
--   Join two components of a planar drawing by one edge
-- statement:
--   For a disconnected graph with a crossing-free drawing, add a single edge between unreachable vertices, retain all old edges, add no other edges, and produce a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_bridge_insertion_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ∃ H : SimpleGraph V,
      ¬ G.Reachable u v ∧
      ¬ G.Adj u v ∧
      H.Adj u v ∧
      (∀ x y, G.Adj x y → H.Adj x y) ∧
      (∀ x y, H.Adj x y →
        G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
