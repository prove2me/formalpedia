-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
-- name    : WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:45.318728+00:00
-- url     : https://prove2.me/theorems/5ff8f1f7-ad05-4a24-a814-a9ee993be8f8
-- title:
--   Add a drawable bridge between disconnected components
-- statement:
--   For every finite disconnected graph with a drawing satisfying the given planar-drawing conditions, there are vertices in different reachable components whose edge can be added while preserving such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V,
      u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
      HasPlanarDrawingOn
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)) := by sorry
