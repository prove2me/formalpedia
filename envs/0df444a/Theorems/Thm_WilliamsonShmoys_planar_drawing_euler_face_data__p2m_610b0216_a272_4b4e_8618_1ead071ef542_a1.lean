-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:59.043976+00:00
-- url     : https://prove2.me/theorems/a4dc4afe-ce6b-457c-8444-aadae7e2d509
-- title:
--   Euler and face data from a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, its directed edges can be partitioned into face-walk fibers with at least three darts per face, and the number of faces satisfies Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (q : ℕ)
      (face : {e : V × V // H.Adj e.1 e.2} → Fin q),
      Fintype.card {e : V × V // H.Adj e.1 e.2} = 2 * H.edgeSet.ncard ∧
      Fintype.card V + q = H.edgeSet.ncard + 2 ∧
      ∀ f : Fin q,
        3 ≤ Fintype.card {d : {e : V × V // H.Adj e.1 e.2} // face d = f} := by sorry
