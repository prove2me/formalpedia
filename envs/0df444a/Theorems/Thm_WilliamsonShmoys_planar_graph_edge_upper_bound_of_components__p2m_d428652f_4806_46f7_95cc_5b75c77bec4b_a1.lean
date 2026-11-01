-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- name    : WilliamsonShmoys.planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:42.230063+00:00
-- url     : https://prove2.me/theorems/24514a04-46c3-4995-8d84-ff88ef385ed2
-- title:
--   Combine connected-component edge bounds
-- statement:
--   If the edge bound holds for every connected finite simple graph with a drawing, then it holds for any finite simple graph with a drawing and at least three vertices. Restrict the drawing to connected components, use the connected bound on components of size at least three, handle components of size one or two directly, and sum their edge counts and vertex counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hconnected : ∀ {U : Type} [Fintype U] [LinearOrder U]
      (N : SimpleGraph U) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card U →
      N.edgeFinset.card ≤ 3 * Fintype.card U - 6)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
