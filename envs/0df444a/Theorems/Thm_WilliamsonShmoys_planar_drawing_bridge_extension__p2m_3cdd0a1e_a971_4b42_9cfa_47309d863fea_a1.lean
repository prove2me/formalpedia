-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension__p2m_3cdd0a1e_a971_4b42_9cfa_47309d863fea_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_extension__p2m_3cdd0a1e_a971_4b42_9cfa_47309d863fea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:08:37.813385+00:00
-- url     : https://prove2.me/theorems/f3b2afb4-7f8b-4821-878f-11c88d67ff5b
-- title:
--   Planar drawing extension by a bridge
-- statement:
--   For vertices in different components of a finite graph with a planar drawing, extend the graph so it remains planar, its edge set strictly grows, and the extension contains the edge joining those vertices. The added adjacency makes the needed bridge explicit; the geometric construction is the child's main obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_bridge_extension__p2m_3cdd0a1e_a971_4b42_9cfa_47309d863fea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hSeparate : ¬ Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet ⊂ H.edgeSet ∧ H.Adj u v := by
  sorry
