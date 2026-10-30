-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:18.541956+00:00
-- url     : https://prove2.me/theorems/1bff0562-92b3-4e82-9dca-3571adbff86f
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite graph with at least three vertices and the specified crossing-free drawing has a natural face count satisfying Euler’s equation. This removes the Euler-count step from the parent. Starting from the given injective noncrossing arcs, a proof must construct the corresponding finite plane embedding and apply Euler’s formula for connected plane graphs. That topological conversion and Euler argument remain to be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
