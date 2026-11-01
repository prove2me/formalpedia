-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:07.873465+00:00
-- url     : https://prove2.me/theorems/bd16beb0-3303-4ae5-9997-6d1ead4b529d
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   An adjacency-maximal graph with a crossing-free drawing and at least three vertices has at least `3|V|−6` edges. A proof route is to obtain a plane embedding from the given drawing, show maximality forces every face to be triangular, and use Euler’s formula. The restriction to at least three vertices is essential for this edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      (∀ u v, M.Adj u v → N.Adj u v) → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
