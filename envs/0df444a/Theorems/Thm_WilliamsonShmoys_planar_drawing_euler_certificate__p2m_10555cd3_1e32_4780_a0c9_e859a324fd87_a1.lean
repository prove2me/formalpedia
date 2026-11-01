-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_certificate__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:35.700784+00:00
-- url     : https://prove2.me/theorems/b9826506-1130-426b-804b-7110284640a9
-- title:
--   Euler certificate from a finite planar drawing
-- statement:
--   A graph with the given crossing-free drawing has a planar simple supergraph on the same vertices that is maximal under adding edges. For at least three vertices, such a maximal planar graph is connected and every face is triangular. Its edge and face counts satisfy Euler’s relation and the face-degree inequality, while its edge count bounds the original graph’s edge count. The augmentation and counting argument must also handle an initially disconnected graph and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_certificate__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ m' f : Nat,
      K.edgeSet.ncard ≤ m' ∧
      Fintype.card U + f = m' + 2 ∧
      3 * f ≤ 2 * m' := by sorry
