-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- name    : WilliamsonShmoys.planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:34.095224+00:00
-- url     : https://prove2.me/theorems/52301ef9-9221-48a8-9b1e-653399277375
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting a crossing-free drawing to a finite vertex subset gives a crossing-free drawing of the induced subgraph. The proof restricts the vertex placement and retains the arcs for edges whose endpoints lie in the subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (S : Finset V) :
    HasPlanarDrawingOn (G.induce (S : Set V)) := by
  sorry
