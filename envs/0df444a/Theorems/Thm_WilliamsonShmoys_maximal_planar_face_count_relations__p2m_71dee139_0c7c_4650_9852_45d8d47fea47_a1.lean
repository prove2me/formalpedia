-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_relations__p2m_71dee139_0c7c_4650_9852_45d8d47fea47_a1
-- name    : WilliamsonShmoys.maximal_planar_face_count_relations__p2m_71dee139_0c7c_4650_9852_45d8d47fea47_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:32.110618+00:00
-- url     : https://prove2.me/theorems/8584d232-b8ae-4ac2-a58e-af76bb6d7665
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a finite drawable graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type, there is a face count f such that triangular face-edge incidence gives 3f = 2E and Euler’s equation gives |V| + f = E + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_count_relations__p2m_71dee139_0c7c_4650_9852_45d8d47fea47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ f : ℕ, 3 * f = 2 * N.edgeFinset.card ∧
      Fintype.card V + f = N.edgeFinset.card + 2 := by sorry
