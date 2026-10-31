-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:51.832211+00:00
-- url     : https://prove2.me/theorems/a18184f7-c783-4d00-9241-7e8764df5618
-- title:
--   Euler and face-boundary counts for a drawable connected graph
-- statement:
--   For a finite connected simple graph with the supplied crossing-free drawing and at least three vertices, there is a face count satisfying Euler’s formula and the aggregate lower bound of three edge sides per face, counting both sides of bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (M.edgeFinset.card : ℤ) + (f : ℤ) = 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card := by sorry
