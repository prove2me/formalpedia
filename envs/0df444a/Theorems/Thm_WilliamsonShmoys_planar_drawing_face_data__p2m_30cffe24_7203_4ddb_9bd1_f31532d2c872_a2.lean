-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:53:24.367954+00:00
-- url     : https://prove2.me/theorems/01a7d165-7651-4131-ac22-8a7ef39ee9e3
-- title:
--   A crossing-free drawing yields finite face-count data
-- statement:
--   For a finite connected simple graph with the supplied crossing-free drawing and at least three vertices, there are natural numbers f and l satisfying Euler’s vertex-edge-face relation, a total face-boundary length of at least three per face, and the incidence count that counts every edge twice. The size hypothesis excludes the small connected cases where a face walk can have length two. This removes the face-counting obligation from the parent. A concrete proof route is to extract a rotation system from the drawing, define faces as cycles of the induced directed-edge permutation, and prove Euler’s formula and the boundary-count facts. The extraction and topological argument remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : ∃ f l : Nat, Fintype.card V + f = K.edgeFinset.card + 2 ∧ 3 * f <= l ∧ l = 2 * K.edgeFinset.card := by sorry
