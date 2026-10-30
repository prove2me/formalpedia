-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:02.584+00:00
-- url     : https://prove2.me/theorems/a3a14366-dd9a-40cc-8d47-64e2f5da9564
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V| − 6 edges. This isolates the topological step needed by the parent: use maximality to establish a triangulation, then Euler’s formula and face-edge incidence counting. The case |V| = 3 yields the triangle’s three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
