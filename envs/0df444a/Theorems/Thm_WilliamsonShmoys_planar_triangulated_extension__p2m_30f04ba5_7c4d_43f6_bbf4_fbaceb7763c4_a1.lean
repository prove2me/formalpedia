-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
-- name    : WilliamsonShmoys.planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:56.459907+00:00
-- url     : https://prove2.me/theorems/28646a36-1b88-4c0c-9520-4ba110528cb4
-- title:
--   Triangulated extension of a finite planar graph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This isolates the triangulating-extension result: choose a drawable supergraph with the most edges, rule out nontriangular faces by adding an edge, then count edges using Euler’s formula. The child handles the graph embedding and counting argument; the parent only uses maximality and antisymmetry. The boundary n=3 is covered by extending to the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
