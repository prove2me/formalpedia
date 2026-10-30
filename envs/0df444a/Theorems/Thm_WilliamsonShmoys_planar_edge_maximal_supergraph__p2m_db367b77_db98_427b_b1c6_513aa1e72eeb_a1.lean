-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:57:37.598843+00:00
-- url     : https://prove2.me/theorems/36b98f67-17ea-4d8a-804d-2453c35e3e7a
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same finite vertex type that is maximal among drawable supergraphs under graph inclusion. Choose a maximal element among the finite collection of drawable supergraphs containing the original graph. This is the finite maximality step and makes no edge-count claim.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by
  sorry
