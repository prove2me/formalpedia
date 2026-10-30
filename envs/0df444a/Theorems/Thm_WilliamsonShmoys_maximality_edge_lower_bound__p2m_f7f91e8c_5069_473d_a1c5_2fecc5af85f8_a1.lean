-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
-- name    : WilliamsonShmoys.maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:14.847559+00:00
-- url     : https://prove2.me/theorems/caf31ad8-7627-4591-a986-7fd32a9eba8e
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable supergraph with additional edges has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := dM;
      3 * Fintype.card V - 6 ≤ M.edgeFinset.card) := by sorry
