-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:03:44.876966+00:00
-- url     : https://prove2.me/theorems/c56f87ad-0620-45d3-bcca-6a52dcb9099e
-- title:
--   Euler and face-incidence equations for maximal planar drawings
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs admits a face count satisfying Euler’s equation and the triangular-face incidence equation. The independent proof route is to establish connectivity and triangular faces from maximality, then apply Euler’s formula and count edge incidences. The boundary case of three vertices is included; the lower bound is necessary for the edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
