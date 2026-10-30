-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:15.32251+00:00
-- url     : https://prove2.me/theorems/ecceac01-0239-445e-a0b3-a366a9290cdc
-- title:
--   Planar simple graph edge bound
-- statement:
--   A drawable finite simple graph with at least three vertices has at most 3|V|−6 edges. This is the Euler-formula bound needed to limit the augmentation process.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
