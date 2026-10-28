-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_components__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
-- name    : WilliamsonShmoys.planar_add_edge_across_components__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:21.374386+00:00
-- url     : https://prove2.me/theorems/add7ccdd-76cf-47f7-b68d-a9139c38be63
-- title:
--   Planar augmentation across components
-- statement:
--   If two distinct vertices lie in different components of a graph with a planar drawing, the graph has a planar supergraph on the same vertices that joins those vertices by an edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

end WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_edge_across_components__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (huv : u ≠ v)
    (hreach : ¬ K.Reachable u v) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ M.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
