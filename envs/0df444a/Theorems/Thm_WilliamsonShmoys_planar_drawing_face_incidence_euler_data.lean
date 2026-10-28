-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_euler_data
-- name    : WilliamsonShmoys.planar_drawing_face_incidence_euler_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:18:18.735353+00:00
-- url     : https://prove2.me/theorems/e0cc44bf-b744-44d9-96d5-ab427541823d
-- title:
--   Euler and face incidence data for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has a finite face count satisfying Euler’s formula; its total face-boundary incidences are twice its edge count, and every face contributes at least three incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_incidence_euler_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : ∀ u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ f i : ℕ,
      Fintype.card V + f = J.edgeSet.ncard + 2 ∧
      3 * f <= i ∧
      i = 2 * J.edgeSet.ncard := by sorry
