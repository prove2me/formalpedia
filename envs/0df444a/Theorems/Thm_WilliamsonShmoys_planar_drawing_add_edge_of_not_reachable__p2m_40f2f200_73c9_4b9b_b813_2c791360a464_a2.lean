-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_not_reachable__p2m_40f2f200_73c9_4b9b_b813_2c791360a464_a2
-- name    : WilliamsonShmoys.planar_drawing_add_edge_of_not_reachable__p2m_40f2f200_73c9_4b9b_b813_2c791360a464_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:18.545426+00:00
-- url     : https://prove2.me/theorems/b6d79b25-6716-4eba-bcd4-ca0880a1694e
-- title:
--   Add an edge between specified unreachable vertices
-- statement:
--   For a planar graph and any two vertices in different reachability components, adding exactly the edge between them yields a planar graph. This supplies the geometric extension step after the parent chooses its disconnectedness witness. The statement is stronger and reusable because it works for every specified unreachable pair; its proof still requires the component redraw and connector construction described above.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_of_not_reachable__p2m_40f2f200_73c9_4b9b_b813_2c791360a464_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ P : SimpleGraph V,
      (∀ x y : V, P.Adj x y ↔
        G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
