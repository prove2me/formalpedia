-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:05.554808+00:00
-- url     : https://prove2.me/theorems/b76599c1-0a89-4269-bf03-ff901f7f247a
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   For any nonempty finite ordered vertex type, a graph with a crossing-free drawing has a supergraph on the same vertices that also has a crossing-free drawing and whose adjacency relation connects every pair by a finite path. This isolates the geometric augmentation argument: repeatedly join distinct drawing components through the complement without creating crossings. The nonempty hypothesis handles the zero-vertex boundary case, where no such connected supergraph is guaranteed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 0 < Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
