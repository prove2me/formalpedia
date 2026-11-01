-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:52:08.201845+00:00
-- url     : https://prove2.me/theorems/e9ff0367-589f-4559-ab47-9b29f52daba8
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable extension on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset ⊆ L.edgeFinset) :
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by sorry
