-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- name    : WilliamsonShmoys.maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:13.522761+00:00
-- url     : https://prove2.me/theorems/f65e11f5-62f3-41fd-b487-d806e91e2eaf
-- title:
--   Maximality fixes the edge count of a drawable supergraph
-- statement:
--   If L is maximal among drawable supergraphs and M is a drawable supergraph of L, their edge-set cardinalities are equal. Maximality gives M ≤ L, so antisymmetry yields equality of graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1 {V : Type} [Fintype V] [LinearOrder V] (L M : SimpleGraph V) (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L) (hLM : L ≤ M) (hMDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : L.edgeSet.ncard = M.edgeSet.ncard := by sorry
