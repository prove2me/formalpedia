-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarMaximalEdgeCount_to_PlanarMapData__p2m_b3eca2bb_f78b_4222_b8fc_fe99bf34c163_a1
-- name    : WilliamsonShmoys.planarMaximalEdgeCount_to_PlanarMapData__p2m_b3eca2bb_f78b_4222_b8fc_fe99bf34c163_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:59.3063+00:00
-- url     : https://prove2.me/theorems/fdf01bce-4f52-4194-9686-49bc92db35b4
-- title:
--   Derive finite face data from the maximal planar edge count
-- statement:
--   For a finite simple graph with at least three vertices and 3|V|−6 edges, there is finite face data satisfying the specified Euler equation and face-degree equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

theorem WilliamsonShmoys.planarMaximalEdgeCount_to_PlanarMapData__p2m_b3eca2bb_f78b_4222_b8fc_fe99bf34c163_a1
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : 3 <= Fintype.card V)
    (hedge : J.edgeFinset.card = 3 * Fintype.card V - 6) :
    Nonempty (@PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 V (inferInstance) J inferInstance) := by sorry
