-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:53.707742+00:00
-- url     : https://prove2.me/theorems/cf44c216-3f6e-4f0d-9ff9-4dc3d94f14d1
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A finite edge-maximal drawable simple graph with at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
