-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3
-- name    : WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:23.850502+00:00
-- url     : https://prove2.me/theorems/50e56593-a0f4-4c81-8add-ca1c096dabb3
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ N : SimpleGraph V, G ≤ N ∧ HasPlanarDrawingOn N ∧ (∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) := by sorry
