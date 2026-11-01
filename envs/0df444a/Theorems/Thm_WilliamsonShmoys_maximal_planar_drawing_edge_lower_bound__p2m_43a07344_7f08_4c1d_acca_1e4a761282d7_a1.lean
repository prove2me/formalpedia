-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:45.356628+00:00
-- url     : https://prove2.me/theorems/4107ac22-c459-487d-9b32-d404a4878a55
-- title:
--   Maximal drawable graphs meet the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that admits no proper drawable edge extension has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
