-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_to_edge_maximal__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
-- name    : WilliamsonShmoys.planar_supergraph_to_edge_maximal__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:31.471404+00:00
-- url     : https://prove2.me/theorems/82c2aaf2-6a2c-4e1e-8fde-a24b1ebfc8b9
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set such that every drawable supergraph of it on that vertex set has no additional edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_to_edge_maximal__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, (∀ u v, G.Adj u v → K.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, (∀ u v, K.Adj u v → L.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn L → (∀ u v, L.Adj u v → K.Adj u v)) := by sorry
