-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
-- name    : WilliamsonShmoys.maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:59.08121+00:00
-- url     : https://prove2.me/theorems/d07e54eb-c4bc-460d-b7df-6d44fa14b7ac
-- title:
--   Completion of a drawable graph to a triangulation-sized supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices having exactly 3|V|−6 edges. A proof route is to extend a planar drawing to a triangulation and count its edges using Euler's formula. This is a substantive completion result, not established by the supplied sources; formalizing the drawing extension and triangulation count is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
