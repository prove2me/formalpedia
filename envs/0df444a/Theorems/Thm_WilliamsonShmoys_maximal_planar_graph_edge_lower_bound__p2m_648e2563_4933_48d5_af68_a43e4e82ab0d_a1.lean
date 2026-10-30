-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:45.576472+00:00
-- url     : https://prove2.me/theorems/6d943741-fae6-4c58-9301-d8625eecfd1e
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal finite graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
