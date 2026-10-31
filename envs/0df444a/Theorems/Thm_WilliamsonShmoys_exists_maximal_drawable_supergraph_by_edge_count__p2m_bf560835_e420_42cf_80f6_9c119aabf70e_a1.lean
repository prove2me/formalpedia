-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:06.084673+00:00
-- url     : https://prove2.me/theorems/1365cfbd-c891-46de-8dfc-122f67bff81e
-- title:
--   A drawable supergraph maximizing edge count
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph whose edge count is at least that of every drawable supergraph of the original graph. The proof route is finite enumeration and maximization; this isolates the finite existence argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard) := by sorry
