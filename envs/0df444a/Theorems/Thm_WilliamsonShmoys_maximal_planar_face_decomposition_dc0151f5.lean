-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_dc0151f5
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_dc0151f5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:58:10.017406+00:00
-- url     : https://prove2.me/theorems/2cbac039-c772-4e1f-aee6-79f02c3a5fd2
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, there is a face count satisfying Euler’s equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_dc0151f5 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → M.edgeSet = L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
