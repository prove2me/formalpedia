-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:54.877135+00:00
-- url     : https://prove2.me/theorems/44372213-62c2-4236-90e5-79abbff6c6bc
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that admits no strict drawable supergraph. This removes the maximality selection step from the parent. An independent proof route is to maximize the edge count among the finitely many supergraphs of G that satisfy HasPlanarDrawingOn; any drawable supergraph of a maximizer must then be equal to it. The argument also covers vertex sets with fewer than three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
