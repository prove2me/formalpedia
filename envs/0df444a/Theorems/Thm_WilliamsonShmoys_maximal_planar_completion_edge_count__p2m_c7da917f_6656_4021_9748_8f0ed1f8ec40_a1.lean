-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:32.744507+00:00
-- url     : https://prove2.me/theorems/7ccdbe8d-8a58-4fea-8872-faa4254f94f9
-- title:
--   Completion of a drawable graph to maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly three times the number of vertices minus six edges. The child preserves the drawing and vertex-count hypotheses and handles disconnected starting graphs as well. Prove it by selecting a drawable supergraph with the maximum number of edges, triangulating its faces, and applying Euler’s formula; the three-vertex case gives the triangle. This removes the parent’s main topological and counting work. The remaining obligation is to formalize that planar completion argument for the arc-based definition of HasPlanarDrawingOn. The child is based on the cited Williamson–Shmoys Theorem 10.11 argument; no matching local Lean proof was available to reuse.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
