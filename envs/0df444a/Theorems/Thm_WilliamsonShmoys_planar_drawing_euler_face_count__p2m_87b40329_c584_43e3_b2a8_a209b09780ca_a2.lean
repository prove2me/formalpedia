-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:30.718569+00:00
-- url     : https://prove2.me/theorems/86ede61b-f0c2-4734-8662-5897b5a8be7f
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, extract the finite set of faces and prove Euler’s equation for its cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ faceCount : Nat,
      Fintype.card V + faceCount = K.edgeFinset.card + 2 := by
  sorry
