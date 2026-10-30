-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:42:37.231461+00:00
-- url     : https://prove2.me/theorems/9dc8cc9d-f679-4564-bf74-5492a4529432
-- title:
--   Planar simple graphs have at most 3n−6 edges
-- statement:
--   For any graph with the given crossing-free drawing and at least three vertices, its edge count is at most `3|V|−6`. This is the standard planar simple graph bound: formalize the Euler inequality for the drawing (or augment to a maximal planar graph and count face-edge incidences), retaining the stated cardinality hypothesis for natural subtraction. This removes the upper-bound half from the parent; the remaining work is the planar Euler/counting argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
