-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:45.903282+00:00
-- url     : https://prove2.me/theorems/e52a5279-3bb4-4190-b470-b345cecfed03
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A simply drawn planar graph with at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (dG : DecidableRel G.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
