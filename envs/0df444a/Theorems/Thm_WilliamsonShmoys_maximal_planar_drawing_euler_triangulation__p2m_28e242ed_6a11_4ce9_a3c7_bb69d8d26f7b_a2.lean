-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:03.157516+00:00
-- url     : https://prove2.me/theorems/93f8b8d0-4b83-43fb-8fbd-8c60dcb96c79
-- title:
--   Euler formula and triangular face incidence for a maximal planar drawing
-- statement:
--   For a maximal crossing-free drawing on at least three vertices, there is a finite face count satisfying Euler’s formula and exact triangular face-edge incidence. The new claim follows by proving maximality forces a connected plane triangulation, including the three-vertex boundary case. Euler’s formula and the incidence equality then imply the target edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    ∃ f : ℕ, Fintype.card V + f = L.edgeFinset.card + 2 ∧
      2 * L.edgeFinset.card = 3 * f := by sorry
