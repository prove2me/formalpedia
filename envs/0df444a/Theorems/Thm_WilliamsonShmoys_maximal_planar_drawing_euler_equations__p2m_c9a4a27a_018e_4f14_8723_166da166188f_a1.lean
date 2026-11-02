-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:39.836592+00:00
-- url     : https://prove2.me/theorems/ab3c4834-8b15-4a63-8fca-25572aaa5eac
-- title:
--   Euler and face-incidence equations for a maximal drawing
-- statement:
--   For a drawable simple graph on at least three finite vertices that is maximal among drawable supergraphs on the same vertices, there is a face count satisfying Euler’s equation and the triangular-face edge-incidence equation. The proof route is to show maximality forces a connected triangulation, then count vertices, edges, faces, and face-edge incidences in its sphere embedding. This removes the geometric face-counting obligation from the parent; the remaining work is formalizing that argument for `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f = 2 * M.edgeFinset.card := by sorry
