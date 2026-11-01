-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_bounds__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count_bounds__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:39.173685+00:00
-- url     : https://prove2.me/theorems/256446b0-8e90-4830-b2d0-cc6afad60048
-- title:
--   Euler and face-length bounds for a maximal planar drawing
-- statement:
--   A maximal planar drawing on at least three vertices has a finite face count f satisfying Euler’s formula and the planar face-boundary incidence inequality. This isolates the topological graph argument needed for the edge lower bound. Prove it by deriving connectedness and triangulation from maximality, then applying Euler’s formula and counting each edge on two face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_count_bounds__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    ∃ f : ℕ, Fintype.card V + f = L.edgeFinset.card + 2 ∧ 3 * f ≤ 2 * L.edgeFinset.card := by sorry
