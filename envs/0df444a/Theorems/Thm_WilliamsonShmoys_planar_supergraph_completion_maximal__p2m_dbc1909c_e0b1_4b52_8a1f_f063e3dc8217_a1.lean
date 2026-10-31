-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- name    : WilliamsonShmoys.planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:42.83641+00:00
-- url     : https://prove2.me/theorems/38617ac2-81d5-4709-9947-cdbb4db2ee10
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs under edge-set inclusion. The finite set of all simple graphs on V permits choosing an inclusion-maximal drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = H) := by sorry
