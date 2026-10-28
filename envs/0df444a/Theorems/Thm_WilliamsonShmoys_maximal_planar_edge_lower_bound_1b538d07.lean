-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_1b538d07
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_1b538d07
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:13:23.17687+00:00
-- url     : https://prove2.me/theorems/d20f5e02-06cc-499c-b877-8b4141c3a91c
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3n−6` edges. This removes the geometric and Euler-counting work from the parent. A proof route is to use the drawing arcs and maximality to establish connectedness and triangular faces, then apply Euler’s formula and count face-edge incidences. Handle `n = 3` as part of the triangulation argument; this hypothesis retains the needed boundary condition. Formalizing the embedding facts for the given continuous injective arcs is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_1b538d07
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → K ≠ L →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
