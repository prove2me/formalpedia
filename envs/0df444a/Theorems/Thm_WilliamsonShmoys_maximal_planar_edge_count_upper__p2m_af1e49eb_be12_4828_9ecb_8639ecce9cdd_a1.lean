-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:58.216044+00:00
-- url     : https://prove2.me/theorems/4414481d-333a-4f96-8a2d-2d6fda1fe3c0
-- title:
--   Euler upper bound for a drawable graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. Prove this from the planar Euler relation and the fact that each face boundary has length at least three, handling disconnected drawings as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
