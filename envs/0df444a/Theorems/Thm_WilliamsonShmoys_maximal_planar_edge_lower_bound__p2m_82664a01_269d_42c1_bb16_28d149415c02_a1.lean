-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:50:21.220203+00:00
-- url     : https://prove2.me/theorems/4f9da5bc-ae01-4349-bf9c-64dbf4d60dbc
-- title:
--   An inclusion-maximal drawable graph meets the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U → T ≤ U → U = T)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
