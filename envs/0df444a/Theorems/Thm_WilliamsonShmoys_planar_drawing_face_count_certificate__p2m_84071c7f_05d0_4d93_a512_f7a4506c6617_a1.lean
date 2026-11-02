-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
-- name    : WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:39.304965+00:00
-- url     : https://prove2.me/theorems/1d70c721-aa53-4057-b653-b3769ca8ce77
-- title:
--   Euler face certificate for a connected drawn graph
-- statement:
--   A finite connected simple graph with the specified planar drawing either has at most |V|−1 edges, or admits finite face-boundary length data satisfying Euler’s formula, total boundary length 2|E|, and boundary length at least 3 for every face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hConnected : K.Connected)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 1 ≤ Fintype.card V ∨
    ∃ (f : ℕ) (boundaryLength : Fin f → ℕ),
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      (∑ i : Fin f, boundaryLength i) = 2 * K.edgeFinset.card ∧
      ∀ i : Fin f, 3 ≤ boundaryLength i := by sorry
