-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4
-- name    : WilliamsonShmoys.maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:48:05.209372+00:00
-- url     : https://prove2.me/theorems/ce063170-d1d4-44ee-8dd5-42d3412301d5
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A finite graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex type, and with at least three vertices, has a face count satisfying Euler’s equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    exists f : Nat,
      Fintype.card V + f = L.edgeFinset.card + 2 ∧
      3 * f = 2 * L.edgeFinset.card := by sorry
