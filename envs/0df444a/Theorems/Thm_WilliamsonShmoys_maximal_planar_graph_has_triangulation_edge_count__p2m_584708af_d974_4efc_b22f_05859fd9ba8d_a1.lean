-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:33.623868+00:00
-- url     : https://prove2.me/theorems/b9f43026-a41c-414f-8846-4d67a85cd361
-- title:
--   Maximal planar graphs have triangulation edge count
-- statement:
--   An inclusion-maximal simple graph admitting the specified planar drawing on a finite linearly ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
