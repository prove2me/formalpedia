-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e2c10b97_84b2_4ddf_bc9b_07844206edcc_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e2c10b97_84b2_4ddf_bc9b_07844206edcc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:59:20.244835+00:00
-- url     : https://prove2.me/theorems/b612304e-8f9c-4158-9b49-2cccd47a0774
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e2c10b97_84b2_4ddf_bc9b_07844206edcc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, M ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
