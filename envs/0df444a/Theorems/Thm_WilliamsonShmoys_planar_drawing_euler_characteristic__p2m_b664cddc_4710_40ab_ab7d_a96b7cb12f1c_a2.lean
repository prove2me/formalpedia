-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:10.23981+00:00
-- url     : https://prove2.me/theorems/c92cb03b-dbf0-412f-b8f6-8a0459655fc8
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the specified crossing-free drawing has a face count satisfying Euler’s vertex-edge-face equation. Connectedness is needed for this form of the equation; no minimum vertex count is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 := by sorry
