-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:07:38.960049+00:00
-- url     : https://prove2.me/theorems/b2f31750-6395-4f01-b4dd-f5215a908d6d
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal planar simple graph on at least three vertices has exactly three times its vertex count minus six edges. This is the topological core needed by the parent; its independent proof route is to extract a finite plane embedding from the given drawing, use Euler's formula, and show maximality forces triangular faces. The result is reusable as an edge-count theorem, while the drawing-to-embedding and triangulation arguments remain the substantial obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
