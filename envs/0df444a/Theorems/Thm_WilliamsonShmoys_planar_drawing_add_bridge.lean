-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge
-- name    : WilliamsonShmoys.planar_drawing_add_bridge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:20:38.555988+00:00
-- url     : https://prove2.me/theorems/a237a486-8467-47f4-bbb9-a4fa3642b241
-- title:
--   Add a planar bridge between disconnected components
-- statement:
--   Extend a finite disconnected graph with the specified planar drawing by an edge between previously disconnected vertices, preserving all old edges and the planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ (∀ u v : V, Nonempty (G.Walk u v))) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ Nonempty (G.Walk u v) ∧ H.Adj u v := by sorry
