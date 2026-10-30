-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_component_bounds__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
-- name    : WilliamsonShmoys.planar_edge_count_upper_of_component_bounds__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:22.806161+00:00
-- url     : https://prove2.me/theorems/1102a824-a934-4a26-844e-abad9808048d
-- title:
--   Aggregate edge bounds over connected components
-- statement:
--   If each component of size at least three satisfies the connected edge bound, then the whole graph satisfies the bound. Sum component edge and vertex counts; use simplicity for components of size one or two, and use the whole-graph cardinality hypothesis to ensure total slack is at least six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_of_component_bounds__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hLocal :
      ∀ c : M.ConnectedComponent, ∀ [Fintype c],
        3 ≤ Fintype.card c →
        (c.toSimpleGraph).edgeSet.ncard + 6 ≤ 3 * Fintype.card c) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
