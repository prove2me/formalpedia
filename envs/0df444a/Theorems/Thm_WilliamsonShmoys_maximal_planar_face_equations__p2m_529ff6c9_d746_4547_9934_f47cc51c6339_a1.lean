-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1
-- name    : WilliamsonShmoys.maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:25:36.560822+00:00
-- url     : https://prove2.me/theorems/5ab9b52f-fdb8-4eff-9a4e-c2dd12c7a0d0
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing, and no strictly larger drawable supergraph on the same vertices, there is a number of faces satisfying Euler’s equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
