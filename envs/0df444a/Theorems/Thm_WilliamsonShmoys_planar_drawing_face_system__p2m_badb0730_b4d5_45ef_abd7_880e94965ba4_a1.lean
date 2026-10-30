-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_system__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
-- name    : WilliamsonShmoys.planar_drawing_face_system__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:22:20.919981+00:00
-- url     : https://prove2.me/theorems/bebb4962-8c14-47c4-9965-36e7f95a6658
-- title:
--   Face system and Euler formula from a planar drawing
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing admits a finite assignment of its directed edges to faces satisfying Euler’s formula, with at least three directed edges assigned to every face. This isolates the topological face-system construction from the separate directed-edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_system__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (q : ℕ)
      (face : {e : V × V // H.Adj e.1 e.2} → Fin q),
      Fintype.card V + q = H.edgeSet.ncard + 2 ∧
      ∀ f : Fin q,
        3 ≤ Fintype.card {d : {e : V × V // H.Adj e.1 e.2} // face d = f} := by sorry
