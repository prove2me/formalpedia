-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
-- name    : WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:08.920771+00:00
-- url     : https://prove2.me/theorems/0a2052a6-a955-4e0d-9ed7-811dd0966187
-- title:
--   Add a drawable bridge when the vertex set has at least three elements
-- statement:
--   A drawable disconnected graph on a finite linearly ordered vertex type with at least three vertices can have an edge added between distinct components while preserving a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V,
      u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
      HasPlanarDrawingOn
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)) := by sorry
