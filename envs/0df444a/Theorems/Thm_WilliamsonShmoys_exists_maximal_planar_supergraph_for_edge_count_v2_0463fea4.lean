-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:03:55.831282+00:00
-- url     : https://prove2.me/theorems/b1095a64-d129-4f41-be47-a2e9dc0505a5
-- title:
--   Existence of a maximal drawable supergraph for the edge-count extension
-- statement:
--   A drawable finite simple graph is contained in a drawable graph on the same vertices that is maximal among drawable supergraphs under edge inclusion. The maximizing drawing may be chosen anew.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        Set.Subset R.edgeSet S.edgeSet →
        S.edgeSet = R.edgeSet := by
  sorry
