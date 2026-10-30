-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:27.069791+00:00
-- url     : https://prove2.me/theorems/badb0730-b4d5-45ef-abd7-880e94965ba4
-- title:
--   Euler and face data from a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a partition of its directed edges into face-walk fibers, with twice as many directed edges as undirected edges, Euler’s equation, and at least three darts in every face fiber.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
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
