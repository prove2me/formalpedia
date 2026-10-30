-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:46:36.866619+00:00
-- url     : https://prove2.me/theorems/3cdd0a1e-a971-4b42-9cfa-47309d863fea
-- title:
--   Add a drawable edge between separate components
-- statement:
--   In a finite planar drawing, vertices in different components can be joined by a new edge while preserving a planar drawing and strictly enlarging the edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hSeparate : ¬ Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet := by sorry
