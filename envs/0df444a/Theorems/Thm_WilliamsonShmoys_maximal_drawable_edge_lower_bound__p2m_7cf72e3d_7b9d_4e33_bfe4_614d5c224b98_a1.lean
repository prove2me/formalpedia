-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:47.912854+00:00
-- url     : https://prove2.me/theorems/2752f1ab-5752-4af7-9412-6b19a571a389
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   For a drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices, the edge count is at least 3n−6. A proof route is to derive connectedness and triangular faces from maximality, then use Euler’s formula and face-edge incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N → HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V <= M.edgeFinset.card + 6 := by sorry
